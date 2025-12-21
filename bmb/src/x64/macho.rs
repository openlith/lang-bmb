//! Mach-O 64-bit Executable Generation
//!
//! Generates minimal macOS x86-64 Mach-O executables.
//! No external linker required.

use std::io::{self, Write};

/// Mach-O file header constants
pub mod consts {
    // Magic numbers
    pub const MH_MAGIC_64: u32 = 0xFEED_FACF; // 64-bit little-endian

    // CPU types
    pub const CPU_TYPE_X86_64: i32 = 0x0100_0007; // CPU_TYPE_X86 | CPU_ARCH_ABI64
    pub const CPU_SUBTYPE_X86_64_ALL: i32 = 3;

    // File types
    pub const MH_EXECUTE: u32 = 2; // Executable

    // Flags
    pub const MH_NOUNDEFS: u32 = 0x0000_0001; // No undefined references
    pub const MH_PIE: u32 = 0x0020_0000; // Position independent executable

    // Load command types
    pub const LC_SEGMENT_64: u32 = 0x19; // 64-bit segment
    pub const LC_MAIN: u32 = 0x8000_0028; // Replacement for LC_UNIXTHREAD

    // Segment protection
    pub const VM_PROT_READ: i32 = 0x01;
    pub const VM_PROT_WRITE: i32 = 0x02;
    pub const VM_PROT_EXECUTE: i32 = 0x04;

    // Segment flags
    pub const S_ATTR_PURE_INSTRUCTIONS: u32 = 0x8000_0000;
    pub const S_ATTR_SOME_INSTRUCTIONS: u32 = 0x0000_0400;

    // Section types
    pub const S_REGULAR: u8 = 0x00;

    // Header sizes
    pub const MACH_HEADER_64_SIZE: u32 = 32;
    pub const SEGMENT_COMMAND_64_SIZE: u32 = 72;
    pub const SECTION_64_SIZE: u32 = 80;
    pub const ENTRY_POINT_COMMAND_SIZE: u32 = 24;

    // Default page size on macOS
    pub const PAGE_SIZE: u64 = 0x4000; // 16KB (Apple Silicon default, x86_64 compatible)
}

/// Mach-O 64-bit header
#[derive(Debug, Clone)]
pub struct MachHeader64 {
    pub magic: u32,
    pub cputype: i32,
    pub cpusubtype: i32,
    pub filetype: u32,
    pub ncmds: u32,
    pub sizeofcmds: u32,
    pub flags: u32,
    pub reserved: u32,
}

impl Default for MachHeader64 {
    fn default() -> Self {
        Self {
            magic: consts::MH_MAGIC_64,
            cputype: consts::CPU_TYPE_X86_64,
            cpusubtype: consts::CPU_SUBTYPE_X86_64_ALL,
            filetype: consts::MH_EXECUTE,
            ncmds: 0,
            sizeofcmds: 0,
            flags: consts::MH_NOUNDEFS | consts::MH_PIE,
            reserved: 0,
        }
    }
}

impl MachHeader64 {
    pub fn write<W: Write>(&self, w: &mut W) -> io::Result<()> {
        w.write_all(&self.magic.to_le_bytes())?;
        w.write_all(&self.cputype.to_le_bytes())?;
        w.write_all(&self.cpusubtype.to_le_bytes())?;
        w.write_all(&self.filetype.to_le_bytes())?;
        w.write_all(&self.ncmds.to_le_bytes())?;
        w.write_all(&self.sizeofcmds.to_le_bytes())?;
        w.write_all(&self.flags.to_le_bytes())?;
        w.write_all(&self.reserved.to_le_bytes())?;
        Ok(())
    }
}

/// LC_SEGMENT_64 load command
#[derive(Debug, Clone)]
pub struct SegmentCommand64 {
    pub cmd: u32,
    pub cmdsize: u32,
    pub segname: [u8; 16],
    pub vmaddr: u64,
    pub vmsize: u64,
    pub fileoff: u64,
    pub filesize: u64,
    pub maxprot: i32,
    pub initprot: i32,
    pub nsects: u32,
    pub flags: u32,
}

impl SegmentCommand64 {
    pub fn new_text_segment() -> Self {
        let mut segname = [0u8; 16];
        segname[..7].copy_from_slice(b"__TEXT\0");

        Self {
            cmd: consts::LC_SEGMENT_64,
            cmdsize: consts::SEGMENT_COMMAND_64_SIZE,
            segname,
            vmaddr: 0,
            vmsize: 0,
            fileoff: 0,
            filesize: 0,
            maxprot: consts::VM_PROT_READ | consts::VM_PROT_EXECUTE,
            initprot: consts::VM_PROT_READ | consts::VM_PROT_EXECUTE,
            nsects: 0,
            flags: 0,
        }
    }

    pub fn new_linkedit_segment() -> Self {
        let mut segname = [0u8; 16];
        segname[..11].copy_from_slice(b"__LINKEDIT\0");

        Self {
            cmd: consts::LC_SEGMENT_64,
            cmdsize: consts::SEGMENT_COMMAND_64_SIZE,
            segname,
            vmaddr: 0,
            vmsize: 0,
            fileoff: 0,
            filesize: 0,
            maxprot: consts::VM_PROT_READ,
            initprot: consts::VM_PROT_READ,
            nsects: 0,
            flags: 0,
        }
    }

    pub fn with_section(mut self) -> Self {
        self.nsects = 1;
        self.cmdsize = consts::SEGMENT_COMMAND_64_SIZE + consts::SECTION_64_SIZE;
        self
    }

    pub fn write<W: Write>(&self, w: &mut W) -> io::Result<()> {
        w.write_all(&self.cmd.to_le_bytes())?;
        w.write_all(&self.cmdsize.to_le_bytes())?;
        w.write_all(&self.segname)?;
        w.write_all(&self.vmaddr.to_le_bytes())?;
        w.write_all(&self.vmsize.to_le_bytes())?;
        w.write_all(&self.fileoff.to_le_bytes())?;
        w.write_all(&self.filesize.to_le_bytes())?;
        w.write_all(&self.maxprot.to_le_bytes())?;
        w.write_all(&self.initprot.to_le_bytes())?;
        w.write_all(&self.nsects.to_le_bytes())?;
        w.write_all(&self.flags.to_le_bytes())?;
        Ok(())
    }
}

/// Section 64-bit structure
#[derive(Debug, Clone)]
pub struct Section64 {
    pub sectname: [u8; 16],
    pub segname: [u8; 16],
    pub addr: u64,
    pub size: u64,
    pub offset: u32,
    pub align: u32,
    pub reloff: u32,
    pub nreloc: u32,
    pub flags: u32,
    pub reserved1: u32,
    pub reserved2: u32,
    pub reserved3: u32,
}

impl Section64 {
    pub fn new_text_section() -> Self {
        let mut sectname = [0u8; 16];
        sectname[..7].copy_from_slice(b"__text\0");
        let mut segname = [0u8; 16];
        segname[..7].copy_from_slice(b"__TEXT\0");

        Self {
            sectname,
            segname,
            addr: 0,
            size: 0,
            offset: 0,
            align: 4, // 2^4 = 16-byte alignment
            reloff: 0,
            nreloc: 0,
            flags: consts::S_ATTR_PURE_INSTRUCTIONS | consts::S_ATTR_SOME_INSTRUCTIONS,
            reserved1: 0,
            reserved2: 0,
            reserved3: 0,
        }
    }

    pub fn write<W: Write>(&self, w: &mut W) -> io::Result<()> {
        w.write_all(&self.sectname)?;
        w.write_all(&self.segname)?;
        w.write_all(&self.addr.to_le_bytes())?;
        w.write_all(&self.size.to_le_bytes())?;
        w.write_all(&self.offset.to_le_bytes())?;
        w.write_all(&self.align.to_le_bytes())?;
        w.write_all(&self.reloff.to_le_bytes())?;
        w.write_all(&self.nreloc.to_le_bytes())?;
        w.write_all(&self.flags.to_le_bytes())?;
        w.write_all(&self.reserved1.to_le_bytes())?;
        w.write_all(&self.reserved2.to_le_bytes())?;
        w.write_all(&self.reserved3.to_le_bytes())?;
        Ok(())
    }
}

/// LC_MAIN entry point command
#[derive(Debug, Clone)]
pub struct EntryPointCommand {
    pub cmd: u32,
    pub cmdsize: u32,
    pub entryoff: u64, // File offset to main()
    pub stacksize: u64,
}

impl Default for EntryPointCommand {
    fn default() -> Self {
        Self {
            cmd: consts::LC_MAIN,
            cmdsize: consts::ENTRY_POINT_COMMAND_SIZE,
            entryoff: 0,
            stacksize: 0,
        }
    }
}

impl EntryPointCommand {
    pub fn write<W: Write>(&self, w: &mut W) -> io::Result<()> {
        w.write_all(&self.cmd.to_le_bytes())?;
        w.write_all(&self.cmdsize.to_le_bytes())?;
        w.write_all(&self.entryoff.to_le_bytes())?;
        w.write_all(&self.stacksize.to_le_bytes())?;
        Ok(())
    }
}

/// Mach-O 64-bit executable builder
#[derive(Debug)]
pub struct MachO64Builder {
    code: Vec<u8>,
}

impl MachO64Builder {
    pub fn new() -> Self {
        Self { code: Vec::new() }
    }

    /// Set the executable code
    pub fn code(mut self, code: Vec<u8>) -> Self {
        self.code = code;
        self
    }

    /// Build the complete Mach-O file
    pub fn build(self) -> Vec<u8> {
        // Calculate sizes
        let header_size = consts::MACH_HEADER_64_SIZE;
        let text_segment_size = consts::SEGMENT_COMMAND_64_SIZE + consts::SECTION_64_SIZE;
        let linkedit_segment_size = consts::SEGMENT_COMMAND_64_SIZE;
        let entry_cmd_size = consts::ENTRY_POINT_COMMAND_SIZE;

        let load_cmds_size = text_segment_size + linkedit_segment_size + entry_cmd_size;
        let header_and_cmds = header_size + load_cmds_size;

        // Align code to page boundary
        let code_offset = align_to(header_and_cmds as u64, 16) as u32; // 16-byte align for code
        let code_size = self.code.len() as u64;

        // __LINKEDIT follows code (empty but required for modern macOS)
        let linkedit_offset = align_to(code_offset as u64 + code_size, 16);
        let linkedit_size = 0u64; // Empty but segment is still required

        let total_file_size = linkedit_offset;
        let vm_size = align_to(total_file_size, consts::PAGE_SIZE);

        // Create header
        let header = MachHeader64 {
            ncmds: 3, // __TEXT, __LINKEDIT, LC_MAIN
            sizeofcmds: load_cmds_size,
            ..Default::default()
        };

        // Create __TEXT segment with __text section
        let mut text_segment = SegmentCommand64::new_text_segment().with_section();
        text_segment.vmaddr = 0x100000000; // Default macOS load address
        text_segment.vmsize = vm_size;
        text_segment.fileoff = 0;
        text_segment.filesize = linkedit_offset;

        let mut text_section = Section64::new_text_section();
        text_section.addr = 0x100000000 + code_offset as u64;
        text_section.size = code_size;
        text_section.offset = code_offset;

        // Create __LINKEDIT segment (required but empty for simple executables)
        let mut linkedit_segment = SegmentCommand64::new_linkedit_segment();
        linkedit_segment.vmaddr = 0x100000000 + linkedit_offset;
        linkedit_segment.vmsize = consts::PAGE_SIZE; // Minimum page
        linkedit_segment.fileoff = linkedit_offset;
        linkedit_segment.filesize = linkedit_size;

        // Create entry point command
        let entry_cmd = EntryPointCommand {
            entryoff: code_offset as u64,
            ..Default::default()
        };

        // Write everything to buffer
        let mut buf = Vec::with_capacity(total_file_size as usize);

        // Header
        header.write(&mut buf).unwrap();

        // Load commands
        text_segment.write(&mut buf).unwrap();
        text_section.write(&mut buf).unwrap();
        linkedit_segment.write(&mut buf).unwrap();
        entry_cmd.write(&mut buf).unwrap();

        // Padding to code offset
        while buf.len() < code_offset as usize {
            buf.push(0);
        }

        // Code
        buf.extend_from_slice(&self.code);

        // Padding to file size
        while buf.len() < total_file_size as usize {
            buf.push(0);
        }

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

impl Default for MachO64Builder {
    fn default() -> Self {
        Self::new()
    }
}

/// Align value up to the next multiple of alignment
fn align_to(value: u64, alignment: u64) -> u64 {
    (value + alignment - 1) & !(alignment - 1)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_mach_header_size() {
        let header = MachHeader64::default();
        let mut buf = Vec::new();
        header.write(&mut buf).unwrap();
        assert_eq!(buf.len(), 32);
    }

    #[test]
    fn test_segment_command_size() {
        let segment = SegmentCommand64::new_text_segment();
        let mut buf = Vec::new();
        segment.write(&mut buf).unwrap();
        assert_eq!(buf.len(), 72);
    }

    #[test]
    fn test_section_size() {
        let section = Section64::new_text_section();
        let mut buf = Vec::new();
        section.write(&mut buf).unwrap();
        assert_eq!(buf.len(), 80);
    }

    #[test]
    fn test_entry_point_command_size() {
        let cmd = EntryPointCommand::default();
        let mut buf = Vec::new();
        cmd.write(&mut buf).unwrap();
        assert_eq!(buf.len(), 24);
    }

    #[test]
    fn test_macho_magic() {
        let builder = MachO64Builder::new().code(vec![0xC3]); // ret
        let macho = builder.build();

        // Check Mach-O magic (little-endian)
        assert_eq!(
            &macho[0..4],
            &[0xCF, 0xFA, 0xED, 0xFE],
            "Should be MH_MAGIC_64"
        );

        // Check CPU type (x86_64)
        let cputype = i32::from_le_bytes([macho[4], macho[5], macho[6], macho[7]]);
        assert_eq!(cputype, consts::CPU_TYPE_X86_64);
    }

    #[test]
    fn test_align_to() {
        assert_eq!(align_to(0, 16), 0);
        assert_eq!(align_to(1, 16), 16);
        assert_eq!(align_to(15, 16), 16);
        assert_eq!(align_to(16, 16), 16);
        assert_eq!(align_to(17, 16), 32);
    }
}
