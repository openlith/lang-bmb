//! ELF64 Generation for ARM64 (Linux AArch64)
//!
//! Creates minimal ELF executables for Linux on ARM64.

use std::io::{self, Write};

/// ELF header constants for ARM64
pub mod consts {
    // ELF magic
    pub const ELF_MAGIC: [u8; 4] = [0x7F, b'E', b'L', b'F'];

    // ELF class
    pub const ELFCLASS64: u8 = 2;

    // ELF data encoding
    pub const ELFDATA2LSB: u8 = 1; // Little endian

    // ELF version
    pub const EV_CURRENT: u8 = 1;

    // OS/ABI
    pub const ELFOSABI_SYSV: u8 = 0;

    // ELF type
    pub const ET_EXEC: u16 = 2;

    // Machine type
    pub const EM_AARCH64: u16 = 183;

    // Program header types
    pub const PT_LOAD: u32 = 1;

    // Segment flags
    pub const PF_X: u32 = 0x1; // Execute
    pub const PF_W: u32 = 0x2; // Write
    pub const PF_R: u32 = 0x4; // Read

    // Sizes
    pub const EHDR_SIZE: u16 = 64;
    pub const PHDR_SIZE: u16 = 56;

    // Default load address for Linux ARM64
    pub const DEFAULT_LOAD_ADDR: u64 = 0x400000;

    // Page size (4KB on Linux ARM64)
    pub const PAGE_SIZE: u64 = 0x1000;
}

/// ELF64 Header for ARM64
#[derive(Debug, Clone)]
pub struct Elf64Header {
    pub e_ident: [u8; 16],
    pub e_type: u16,
    pub e_machine: u16,
    pub e_version: u32,
    pub e_entry: u64,
    pub e_phoff: u64,
    pub e_shoff: u64,
    pub e_flags: u32,
    pub e_ehsize: u16,
    pub e_phentsize: u16,
    pub e_phnum: u16,
    pub e_shentsize: u16,
    pub e_shnum: u16,
    pub e_shstrndx: u16,
}

impl Default for Elf64Header {
    fn default() -> Self {
        let mut e_ident = [0u8; 16];
        e_ident[0..4].copy_from_slice(&consts::ELF_MAGIC);
        e_ident[4] = consts::ELFCLASS64;
        e_ident[5] = consts::ELFDATA2LSB;
        e_ident[6] = consts::EV_CURRENT;
        e_ident[7] = consts::ELFOSABI_SYSV;

        Self {
            e_ident,
            e_type: consts::ET_EXEC,
            e_machine: consts::EM_AARCH64,
            e_version: 1,
            e_entry: 0,
            e_phoff: consts::EHDR_SIZE as u64,
            e_shoff: 0,
            e_flags: 0,
            e_ehsize: consts::EHDR_SIZE,
            e_phentsize: consts::PHDR_SIZE,
            e_phnum: 1,
            e_shentsize: 0,
            e_shnum: 0,
            e_shstrndx: 0,
        }
    }
}

impl Elf64Header {
    pub fn write<W: Write>(&self, w: &mut W) -> io::Result<()> {
        w.write_all(&self.e_ident)?;
        w.write_all(&self.e_type.to_le_bytes())?;
        w.write_all(&self.e_machine.to_le_bytes())?;
        w.write_all(&self.e_version.to_le_bytes())?;
        w.write_all(&self.e_entry.to_le_bytes())?;
        w.write_all(&self.e_phoff.to_le_bytes())?;
        w.write_all(&self.e_shoff.to_le_bytes())?;
        w.write_all(&self.e_flags.to_le_bytes())?;
        w.write_all(&self.e_ehsize.to_le_bytes())?;
        w.write_all(&self.e_phentsize.to_le_bytes())?;
        w.write_all(&self.e_phnum.to_le_bytes())?;
        w.write_all(&self.e_shentsize.to_le_bytes())?;
        w.write_all(&self.e_shnum.to_le_bytes())?;
        w.write_all(&self.e_shstrndx.to_le_bytes())?;
        Ok(())
    }
}

/// ELF64 Program Header
#[derive(Debug, Clone)]
pub struct Elf64ProgramHeader {
    pub p_type: u32,
    pub p_flags: u32,
    pub p_offset: u64,
    pub p_vaddr: u64,
    pub p_paddr: u64,
    pub p_filesz: u64,
    pub p_memsz: u64,
    pub p_align: u64,
}

impl Elf64ProgramHeader {
    pub fn new_load() -> Self {
        Self {
            p_type: consts::PT_LOAD,
            p_flags: consts::PF_R | consts::PF_X,
            p_offset: 0,
            p_vaddr: consts::DEFAULT_LOAD_ADDR,
            p_paddr: consts::DEFAULT_LOAD_ADDR,
            p_filesz: 0,
            p_memsz: 0,
            p_align: consts::PAGE_SIZE,
        }
    }

    pub fn write<W: Write>(&self, w: &mut W) -> io::Result<()> {
        w.write_all(&self.p_type.to_le_bytes())?;
        w.write_all(&self.p_flags.to_le_bytes())?;
        w.write_all(&self.p_offset.to_le_bytes())?;
        w.write_all(&self.p_vaddr.to_le_bytes())?;
        w.write_all(&self.p_paddr.to_le_bytes())?;
        w.write_all(&self.p_filesz.to_le_bytes())?;
        w.write_all(&self.p_memsz.to_le_bytes())?;
        w.write_all(&self.p_align.to_le_bytes())?;
        Ok(())
    }
}

/// ARM64 ELF64 Builder
#[derive(Debug)]
pub struct Arm64Elf64Builder {
    code: Vec<u8>,
}

impl Arm64Elf64Builder {
    pub fn new() -> Self {
        Self { code: Vec::new() }
    }

    /// Set the executable code
    pub fn code(mut self, code: Vec<u8>) -> Self {
        self.code = code;
        self
    }

    /// Build the complete ELF file
    pub fn build(self) -> Vec<u8> {
        let header_size = consts::EHDR_SIZE as u64;
        let phdr_size = consts::PHDR_SIZE as u64;

        // Code starts immediately after headers
        let code_offset = header_size + phdr_size;
        let code_size = self.code.len() as u64;

        // Total file size
        let total_size = code_offset + code_size;

        // Entry point is start of code in virtual memory
        let entry_point = consts::DEFAULT_LOAD_ADDR + code_offset;

        // Create header
        let mut header = Elf64Header::default();
        header.e_entry = entry_point;

        // Create program header
        let mut phdr = Elf64ProgramHeader::new_load();
        phdr.p_filesz = total_size;
        phdr.p_memsz = total_size;

        // Build the file
        let mut buf = Vec::with_capacity(total_size as usize);

        // Write ELF header
        header.write(&mut buf).unwrap();

        // Write program header
        phdr.write(&mut buf).unwrap();

        // Write code
        buf.extend_from_slice(&self.code);

        buf
    }

    /// Build and write to a file
    pub fn write_to_file(self, path: &std::path::Path) -> io::Result<()> {
        use std::fs::File;

        let data = self.build();
        let mut file = File::create(path)?;
        file.write_all(&data)?;

        // Make executable on Unix
        #[cfg(unix)]
        {
            use std::os::unix::fs::PermissionsExt;
            let mut perms = file.metadata()?.permissions();
            perms.set_mode(0o755);
            std::fs::set_permissions(path, perms)?;
        }

        Ok(())
    }
}

impl Default for Arm64Elf64Builder {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_elf_header_size() {
        let header = Elf64Header::default();
        let mut buf = Vec::new();
        header.write(&mut buf).unwrap();
        assert_eq!(buf.len(), 64);
    }

    #[test]
    fn test_program_header_size() {
        let phdr = Elf64ProgramHeader::new_load();
        let mut buf = Vec::new();
        phdr.write(&mut buf).unwrap();
        assert_eq!(buf.len(), 56);
    }

    #[test]
    fn test_elf_magic() {
        // Simple ARM64 program: mov x0, #42; mov x8, #93; svc #0
        let code = vec![
            0x40, 0x05, 0x80, 0xD2, // mov x0, #42
            0xA8, 0x0B, 0x80, 0xD2, // mov x8, #93
            0x01, 0x00, 0x00, 0xD4, // svc #0
        ];

        let elf = Arm64Elf64Builder::new().code(code).build();

        // Check ELF magic
        assert_eq!(&elf[0..4], &[0x7F, b'E', b'L', b'F']);

        // Check ARM64 machine type
        let machine = u16::from_le_bytes([elf[18], elf[19]]);
        assert_eq!(machine, consts::EM_AARCH64);
    }

    #[test]
    fn test_entry_point() {
        let code = vec![0x00; 16]; // Dummy code
        let elf = Arm64Elf64Builder::new().code(code).build();

        // Entry point should be at load address + headers
        let entry = u64::from_le_bytes([
            elf[24], elf[25], elf[26], elf[27], elf[28], elf[29], elf[30], elf[31],
        ]);

        let expected = consts::DEFAULT_LOAD_ADDR + consts::EHDR_SIZE as u64 + consts::PHDR_SIZE as u64;
        assert_eq!(entry, expected);
    }
}
