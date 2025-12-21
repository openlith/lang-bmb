//! ELF64 Executable Generation
//!
//! Generates minimal Linux x86-64 ELF executables.
//! No external linker required.

use std::io::{self, Write};

/// ELF64 file header constants
pub mod consts {
    // ELF magic number
    pub const ELF_MAGIC: [u8; 4] = [0x7F, b'E', b'L', b'F'];

    // ELF class
    pub const ELFCLASS64: u8 = 2;

    // Data encoding
    pub const ELFDATA2LSB: u8 = 1; // Little endian

    // ELF version
    pub const EV_CURRENT: u8 = 1;

    // OS/ABI
    pub const ELFOSABI_NONE: u8 = 0; // UNIX System V ABI

    // Object file type
    pub const ET_EXEC: u16 = 2; // Executable file

    // Machine type
    pub const EM_X86_64: u16 = 62;

    // Program header types
    pub const PT_LOAD: u32 = 1;

    // Program header flags
    pub const PF_X: u32 = 1; // Execute
    pub const PF_W: u32 = 2; // Write
    pub const PF_R: u32 = 4; // Read

    // Header sizes
    pub const ELF64_EHDR_SIZE: u16 = 64;
    pub const ELF64_PHDR_SIZE: u16 = 56;

    // Default load address for Linux x86-64
    pub const DEFAULT_LOAD_ADDR: u64 = 0x400000;
}

/// ELF64 file header
#[derive(Debug, Clone)]
pub struct Elf64Header {
    pub e_type: u16,      // Object file type
    pub e_machine: u16,   // Machine type
    pub e_version: u32,   // Object file version
    pub e_entry: u64,     // Entry point address
    pub e_phoff: u64,     // Program header offset
    pub e_shoff: u64,     // Section header offset
    pub e_flags: u32,     // Processor-specific flags
    pub e_ehsize: u16,    // ELF header size
    pub e_phentsize: u16, // Program header entry size
    pub e_phnum: u16,     // Number of program headers
    pub e_shentsize: u16, // Section header entry size
    pub e_shnum: u16,     // Number of section headers
    pub e_shstrndx: u16,  // Section name string table index
}

impl Default for Elf64Header {
    fn default() -> Self {
        Self {
            e_type: consts::ET_EXEC,
            e_machine: consts::EM_X86_64,
            e_version: consts::EV_CURRENT as u32,
            e_entry: 0,
            e_phoff: consts::ELF64_EHDR_SIZE as u64,
            e_shoff: 0, // No section headers for minimal executable
            e_flags: 0,
            e_ehsize: consts::ELF64_EHDR_SIZE,
            e_phentsize: consts::ELF64_PHDR_SIZE,
            e_phnum: 1,
            e_shentsize: 0,
            e_shnum: 0,
            e_shstrndx: 0,
        }
    }
}

impl Elf64Header {
    pub fn write<W: Write>(&self, w: &mut W) -> io::Result<()> {
        // e_ident (16 bytes)
        w.write_all(&consts::ELF_MAGIC)?;
        w.write_all(&[consts::ELFCLASS64])?; // EI_CLASS
        w.write_all(&[consts::ELFDATA2LSB])?; // EI_DATA
        w.write_all(&[consts::EV_CURRENT])?; // EI_VERSION
        w.write_all(&[consts::ELFOSABI_NONE])?; // EI_OSABI
        w.write_all(&[0u8; 8])?; // EI_PAD

        // Rest of header
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

/// ELF64 program header
#[derive(Debug, Clone)]
pub struct Elf64ProgramHeader {
    pub p_type: u32,   // Segment type
    pub p_flags: u32,  // Segment flags
    pub p_offset: u64, // Segment file offset
    pub p_vaddr: u64,  // Segment virtual address
    pub p_paddr: u64,  // Segment physical address
    pub p_filesz: u64, // Segment size in file
    pub p_memsz: u64,  // Segment size in memory
    pub p_align: u64,  // Segment alignment
}

impl Elf64ProgramHeader {
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

/// ELF64 executable builder
#[derive(Debug)]
pub struct Elf64Builder {
    load_addr: u64,
    code: Vec<u8>,
}

impl Elf64Builder {
    pub fn new() -> Self {
        Self {
            load_addr: consts::DEFAULT_LOAD_ADDR,
            code: Vec::new(),
        }
    }

    /// Set the load address (default: 0x400000)
    pub fn load_addr(mut self, addr: u64) -> Self {
        self.load_addr = addr;
        self
    }

    /// Set the executable code
    pub fn code(mut self, code: Vec<u8>) -> Self {
        self.code = code;
        self
    }

    /// Calculate the entry point address
    fn entry_point(&self) -> u64 {
        // Code starts after ELF header and program header
        let headers_size = consts::ELF64_EHDR_SIZE as u64 + consts::ELF64_PHDR_SIZE as u64;
        self.load_addr + headers_size
    }

    /// Build the complete ELF file
    pub fn build(self) -> Vec<u8> {
        let headers_size = consts::ELF64_EHDR_SIZE as u64 + consts::ELF64_PHDR_SIZE as u64;
        let total_size = headers_size + self.code.len() as u64;

        // Create ELF header
        let ehdr = Elf64Header {
            e_entry: self.entry_point(),
            ..Default::default()
        };

        // Create program header for loadable segment
        let phdr = Elf64ProgramHeader {
            p_type: consts::PT_LOAD,
            p_flags: consts::PF_R | consts::PF_X, // Read + Execute
            p_offset: 0,
            p_vaddr: self.load_addr,
            p_paddr: self.load_addr,
            p_filesz: total_size,
            p_memsz: total_size,
            p_align: 0x1000, // 4KB page alignment
        };

        // Write everything to buffer
        let mut buf = Vec::with_capacity(total_size as usize);
        ehdr.write(&mut buf).unwrap();
        phdr.write(&mut buf).unwrap();
        buf.extend_from_slice(&self.code);

        buf
    }

    /// Build and write to a file
    pub fn write_to_file(self, path: &std::path::Path) -> io::Result<()> {
        use std::fs::File;

        let data = self.build();
        let mut file = File::create(path)?;
        file.write_all(&data)?;

        // Make executable (chmod +x) - Unix only
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

impl Default for Elf64Builder {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_elf_header_size() {
        let ehdr = Elf64Header::default();
        let mut buf = Vec::new();
        ehdr.write(&mut buf).unwrap();
        assert_eq!(buf.len(), 64);
    }

    #[test]
    fn test_program_header_size() {
        let phdr = Elf64ProgramHeader {
            p_type: consts::PT_LOAD,
            p_flags: consts::PF_R | consts::PF_X,
            p_offset: 0,
            p_vaddr: 0x400000,
            p_paddr: 0x400000,
            p_filesz: 120,
            p_memsz: 120,
            p_align: 0x1000,
        };
        let mut buf = Vec::new();
        phdr.write(&mut buf).unwrap();
        assert_eq!(buf.len(), 56);
    }

    #[test]
    fn test_elf_magic() {
        let builder = Elf64Builder::new().code(vec![0xC3]); // ret
        let elf = builder.build();

        // Check ELF magic
        assert_eq!(&elf[0..4], &[0x7F, b'E', b'L', b'F']);

        // Check class (64-bit)
        assert_eq!(elf[4], 2);

        // Check data encoding (little endian)
        assert_eq!(elf[5], 1);
    }

    #[test]
    fn test_entry_point() {
        let builder = Elf64Builder::new().code(vec![0xC3]);
        let entry = builder.entry_point();
        // Entry should be load_addr + headers (64 + 56 = 120 = 0x78)
        assert_eq!(entry, 0x400000 + 120);
    }
}
