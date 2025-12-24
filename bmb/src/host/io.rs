//! File I/O host functions for BMB runtime (v0.13+)
//!
//! Provides standard I/O operations that BMB programs can call via `xcall`.
//! These are designed to be imported by WASM hosts.
//!
//! # Error Codes
//! - -1: General error
//! - -2: File not found
//! - -3: Permission denied
//! - -4: Out of memory
//! - -5: Invalid argument
//! - -6: Too many open files

use std::collections::HashMap;
use std::fs::File;
use std::io::{Read, Seek, SeekFrom, Write};
use std::sync::{Arc, Mutex};

/// File I/O error codes
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum IoError {
    GeneralError = -1,
    FileNotFound = -2,
    PermissionDenied = -3,
    OutOfMemory = -4,
    InvalidArgument = -5,
    TooManyOpenFiles = -6,
}

impl From<std::io::Error> for IoError {
    fn from(e: std::io::Error) -> Self {
        use std::io::ErrorKind;
        match e.kind() {
            ErrorKind::NotFound => IoError::FileNotFound,
            ErrorKind::PermissionDenied => IoError::PermissionDenied,
            ErrorKind::OutOfMemory => IoError::OutOfMemory,
            ErrorKind::InvalidInput => IoError::InvalidArgument,
            _ => IoError::GeneralError,
        }
    }
}

/// Open mode for files
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum OpenMode {
    Read = 0,
    Write = 1,
    Append = 2,
    ReadWrite = 3,
}

impl TryFrom<i32> for OpenMode {
    type Error = IoError;

    fn try_from(value: i32) -> Result<Self, Self::Error> {
        match value {
            0 => Ok(OpenMode::Read),
            1 => Ok(OpenMode::Write),
            2 => Ok(OpenMode::Append),
            3 => Ok(OpenMode::ReadWrite),
            _ => Err(IoError::InvalidArgument),
        }
    }
}

/// Seek origin for io_seek
#[derive(Debug, Clone, Copy)]
pub enum SeekWhence {
    Start = 0,
    Current = 1,
    End = 2,
}

impl TryFrom<i32> for SeekWhence {
    type Error = IoError;

    fn try_from(value: i32) -> Result<Self, Self::Error> {
        match value {
            0 => Ok(SeekWhence::Start),
            1 => Ok(SeekWhence::Current),
            2 => Ok(SeekWhence::End),
            _ => Err(IoError::InvalidArgument),
        }
    }
}

/// File handle table for managing open files
#[derive(Default)]
pub struct FileTable {
    files: HashMap<i32, File>,
    next_fd: i32,
}

impl FileTable {
    /// Create a new file table
    /// FDs 0-2 are reserved for stdin/stdout/stderr
    pub fn new() -> Self {
        Self {
            files: HashMap::new(),
            next_fd: 3,
        }
    }

    /// Open a file and return a file descriptor
    pub fn open(&mut self, path: &str, mode: OpenMode) -> Result<i32, IoError> {
        use std::fs::OpenOptions;

        let file = match mode {
            OpenMode::Read => File::open(path)?,
            OpenMode::Write => OpenOptions::new()
                .write(true)
                .create(true)
                .truncate(true)
                .open(path)?,
            OpenMode::Append => OpenOptions::new()
                .write(true)
                .create(true)
                .append(true)
                .open(path)?,
            OpenMode::ReadWrite => OpenOptions::new()
                .read(true)
                .write(true)
                .create(true)
                .open(path)?,
        };

        let fd = self.next_fd;
        self.next_fd += 1;
        self.files.insert(fd, file);
        Ok(fd)
    }

    /// Read from a file descriptor
    pub fn read(&mut self, fd: i32, buf: &mut [u8]) -> Result<usize, IoError> {
        let file = self.files.get_mut(&fd).ok_or(IoError::InvalidArgument)?;
        let n = file.read(buf)?;
        Ok(n)
    }

    /// Write to a file descriptor
    pub fn write(&mut self, fd: i32, buf: &[u8]) -> Result<usize, IoError> {
        let file = self.files.get_mut(&fd).ok_or(IoError::InvalidArgument)?;
        let n = file.write(buf)?;
        Ok(n)
    }

    /// Close a file descriptor
    pub fn close(&mut self, fd: i32) -> Result<(), IoError> {
        self.files.remove(&fd).ok_or(IoError::InvalidArgument)?;
        Ok(())
    }

    /// Get file size
    pub fn size(&self, fd: i32) -> Result<u64, IoError> {
        let file = self.files.get(&fd).ok_or(IoError::InvalidArgument)?;
        let metadata = file.metadata()?;
        Ok(metadata.len())
    }

    /// Seek in file
    pub fn seek(&mut self, fd: i32, offset: i64, whence: SeekWhence) -> Result<u64, IoError> {
        let file = self.files.get_mut(&fd).ok_or(IoError::InvalidArgument)?;
        let pos = match whence {
            SeekWhence::Start => SeekFrom::Start(offset as u64),
            SeekWhence::Current => SeekFrom::Current(offset),
            SeekWhence::End => SeekFrom::End(offset),
        };
        let new_pos = file.seek(pos)?;
        Ok(new_pos)
    }

    /// Flush file buffers
    pub fn flush(&mut self, fd: i32) -> Result<(), IoError> {
        let file = self.files.get_mut(&fd).ok_or(IoError::InvalidArgument)?;
        file.flush()?;
        Ok(())
    }
}

/// Check if a file exists
pub fn file_exists(path: &str) -> bool {
    std::path::Path::new(path).exists()
}

/// Thread-safe file table wrapper
pub type SharedFileTable = Arc<Mutex<FileTable>>;

/// Create a new shared file table
pub fn new_shared_file_table() -> SharedFileTable {
    Arc::new(Mutex::new(FileTable::new()))
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::io::Write;

    #[test]
    fn test_open_mode_conversion() {
        assert_eq!(OpenMode::try_from(0), Ok(OpenMode::Read));
        assert_eq!(OpenMode::try_from(1), Ok(OpenMode::Write));
        assert_eq!(OpenMode::try_from(4), Err(IoError::InvalidArgument));
    }

    #[test]
    fn test_file_table_read_write() {
        let mut table = FileTable::new();

        // Create temp file
        let temp_path = std::env::temp_dir().join("bmb_io_test.txt");
        let path_str = temp_path.to_str().unwrap();

        // Write
        let fd = table.open(path_str, OpenMode::Write).unwrap();
        table.write(fd, b"hello world").unwrap();
        table.close(fd).unwrap();

        // Read back
        let fd = table.open(path_str, OpenMode::Read).unwrap();
        let mut buf = [0u8; 11];
        let n = table.read(fd, &mut buf).unwrap();
        assert_eq!(n, 11);
        assert_eq!(&buf, b"hello world");
        table.close(fd).unwrap();

        // Cleanup
        std::fs::remove_file(temp_path).ok();
    }

    #[test]
    fn test_file_exists() {
        assert!(file_exists("."));
        assert!(!file_exists("nonexistent_file_12345.txt"));
    }
}
