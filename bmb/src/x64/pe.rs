//! PE (Portable Executable) Generation for Windows x64
//!
//! Generates minimal Windows x64 PE executables.
//! No external linker required.

use std::io::{self, Write};

/// PE file constants
pub mod consts {
    // DOS Header magic
    pub const DOS_MAGIC: u16 = 0x5A4D; // "MZ"

    // PE Signature
    pub const PE_SIGNATURE: u32 = 0x00004550; // "PE\0\0"

    // Machine types
    pub const IMAGE_FILE_MACHINE_AMD64: u16 = 0x8664;

    // File characteristics
    pub const IMAGE_FILE_EXECUTABLE_IMAGE: u16 = 0x0002;
    pub const IMAGE_FILE_LARGE_ADDRESS_AWARE: u16 = 0x0020;

    // Optional header magic
    pub const PE32_PLUS_MAGIC: u16 = 0x020B; // PE32+ (64-bit)

    // Subsystem
    pub const IMAGE_SUBSYSTEM_WINDOWS_CUI: u16 = 3; // Console application

    // DLL characteristics
    pub const IMAGE_DLLCHARACTERISTICS_HIGH_ENTROPY_VA: u16 = 0x0020;
    pub const IMAGE_DLLCHARACTERISTICS_DYNAMIC_BASE: u16 = 0x0040;
    pub const IMAGE_DLLCHARACTERISTICS_NX_COMPAT: u16 = 0x0100;
    pub const IMAGE_DLLCHARACTERISTICS_TERMINAL_SERVER_AWARE: u16 = 0x8000;

    // Section characteristics
    pub const IMAGE_SCN_CNT_CODE: u32 = 0x00000020;
    pub const IMAGE_SCN_CNT_INITIALIZED_DATA: u32 = 0x00000040;
    pub const IMAGE_SCN_MEM_EXECUTE: u32 = 0x20000000;
    pub const IMAGE_SCN_MEM_READ: u32 = 0x40000000;
    pub const IMAGE_SCN_MEM_WRITE: u32 = 0x80000000;

    // Data directory indices
    pub const IMAGE_DIRECTORY_ENTRY_IMPORT: usize = 1;
    pub const IMAGE_DIRECTORY_ENTRY_IAT: usize = 12;

    // Sizes
    pub const DOS_HEADER_SIZE: usize = 64;
    pub const COFF_HEADER_SIZE: usize = 20;
    pub const OPTIONAL_HEADER_SIZE: usize = 240; // PE32+ optional header
    pub const SECTION_HEADER_SIZE: usize = 40;
    pub const DATA_DIRECTORY_COUNT: usize = 16;

    // Alignment
    pub const SECTION_ALIGNMENT: u32 = 0x1000; // 4KB
    pub const FILE_ALIGNMENT: u32 = 0x200; // 512 bytes

    // Default image base for 64-bit
    pub const DEFAULT_IMAGE_BASE: u64 = 0x140000000;
}

/// DOS Header (64 bytes)
#[derive(Debug, Clone)]
pub struct DosHeader {
    pub e_magic: u16,  // Magic number (MZ)
    pub e_lfanew: u32, // File address of PE header
}

impl DosHeader {
    pub fn new(pe_header_offset: u32) -> Self {
        Self {
            e_magic: consts::DOS_MAGIC,
            e_lfanew: pe_header_offset,
        }
    }

    pub fn write<W: Write>(&self, w: &mut W) -> io::Result<()> {
        // e_magic
        w.write_all(&self.e_magic.to_le_bytes())?;
        // e_cblp through e_ovno (58 bytes of mostly zeros)
        w.write_all(&[0u8; 58])?;
        // e_lfanew at offset 60
        w.write_all(&self.e_lfanew.to_le_bytes())?;
        Ok(())
    }
}

/// COFF File Header (20 bytes)
#[derive(Debug, Clone)]
pub struct CoffHeader {
    pub machine: u16,
    pub number_of_sections: u16,
    pub time_date_stamp: u32,
    pub pointer_to_symbol_table: u32,
    pub number_of_symbols: u32,
    pub size_of_optional_header: u16,
    pub characteristics: u16,
}

impl CoffHeader {
    pub fn new(num_sections: u16) -> Self {
        Self {
            machine: consts::IMAGE_FILE_MACHINE_AMD64,
            number_of_sections: num_sections,
            time_date_stamp: 0,
            pointer_to_symbol_table: 0,
            number_of_symbols: 0,
            size_of_optional_header: consts::OPTIONAL_HEADER_SIZE as u16,
            characteristics: consts::IMAGE_FILE_EXECUTABLE_IMAGE
                | consts::IMAGE_FILE_LARGE_ADDRESS_AWARE,
        }
    }

    pub fn write<W: Write>(&self, w: &mut W) -> io::Result<()> {
        w.write_all(&self.machine.to_le_bytes())?;
        w.write_all(&self.number_of_sections.to_le_bytes())?;
        w.write_all(&self.time_date_stamp.to_le_bytes())?;
        w.write_all(&self.pointer_to_symbol_table.to_le_bytes())?;
        w.write_all(&self.number_of_symbols.to_le_bytes())?;
        w.write_all(&self.size_of_optional_header.to_le_bytes())?;
        w.write_all(&self.characteristics.to_le_bytes())?;
        Ok(())
    }
}

/// Data Directory entry
#[derive(Debug, Clone, Copy, Default)]
pub struct DataDirectory {
    pub virtual_address: u32,
    pub size: u32,
}

impl DataDirectory {
    pub fn write<W: Write>(&self, w: &mut W) -> io::Result<()> {
        w.write_all(&self.virtual_address.to_le_bytes())?;
        w.write_all(&self.size.to_le_bytes())?;
        Ok(())
    }
}

/// Optional Header (PE32+, 240 bytes)
#[derive(Debug, Clone)]
pub struct OptionalHeader {
    // Standard fields
    pub magic: u16,
    pub major_linker_version: u8,
    pub minor_linker_version: u8,
    pub size_of_code: u32,
    pub size_of_initialized_data: u32,
    pub size_of_uninitialized_data: u32,
    pub address_of_entry_point: u32,
    pub base_of_code: u32,

    // PE32+ fields
    pub image_base: u64,
    pub section_alignment: u32,
    pub file_alignment: u32,
    pub major_os_version: u16,
    pub minor_os_version: u16,
    pub major_image_version: u16,
    pub minor_image_version: u16,
    pub major_subsystem_version: u16,
    pub minor_subsystem_version: u16,
    pub win32_version_value: u32,
    pub size_of_image: u32,
    pub size_of_headers: u32,
    pub checksum: u32,
    pub subsystem: u16,
    pub dll_characteristics: u16,
    pub size_of_stack_reserve: u64,
    pub size_of_stack_commit: u64,
    pub size_of_heap_reserve: u64,
    pub size_of_heap_commit: u64,
    pub loader_flags: u32,
    pub number_of_rva_and_sizes: u32,

    // Data directories
    pub data_directories: [DataDirectory; consts::DATA_DIRECTORY_COUNT],
}

impl Default for OptionalHeader {
    fn default() -> Self {
        Self {
            magic: consts::PE32_PLUS_MAGIC,
            major_linker_version: 14,
            minor_linker_version: 0,
            size_of_code: 0,
            size_of_initialized_data: 0,
            size_of_uninitialized_data: 0,
            address_of_entry_point: 0,
            base_of_code: 0,
            image_base: consts::DEFAULT_IMAGE_BASE,
            section_alignment: consts::SECTION_ALIGNMENT,
            file_alignment: consts::FILE_ALIGNMENT,
            major_os_version: 6,
            minor_os_version: 0,
            major_image_version: 0,
            minor_image_version: 0,
            major_subsystem_version: 6,
            minor_subsystem_version: 0,
            win32_version_value: 0,
            size_of_image: 0,
            size_of_headers: 0,
            checksum: 0,
            subsystem: consts::IMAGE_SUBSYSTEM_WINDOWS_CUI,
            dll_characteristics: consts::IMAGE_DLLCHARACTERISTICS_HIGH_ENTROPY_VA
                | consts::IMAGE_DLLCHARACTERISTICS_DYNAMIC_BASE
                | consts::IMAGE_DLLCHARACTERISTICS_NX_COMPAT
                | consts::IMAGE_DLLCHARACTERISTICS_TERMINAL_SERVER_AWARE,
            size_of_stack_reserve: 0x100000,
            size_of_stack_commit: 0x1000,
            size_of_heap_reserve: 0x100000,
            size_of_heap_commit: 0x1000,
            loader_flags: 0,
            number_of_rva_and_sizes: consts::DATA_DIRECTORY_COUNT as u32,
            data_directories: [DataDirectory::default(); consts::DATA_DIRECTORY_COUNT],
        }
    }
}

impl OptionalHeader {
    pub fn write<W: Write>(&self, w: &mut W) -> io::Result<()> {
        w.write_all(&self.magic.to_le_bytes())?;
        w.write_all(&[self.major_linker_version, self.minor_linker_version])?;
        w.write_all(&self.size_of_code.to_le_bytes())?;
        w.write_all(&self.size_of_initialized_data.to_le_bytes())?;
        w.write_all(&self.size_of_uninitialized_data.to_le_bytes())?;
        w.write_all(&self.address_of_entry_point.to_le_bytes())?;
        w.write_all(&self.base_of_code.to_le_bytes())?;
        w.write_all(&self.image_base.to_le_bytes())?;
        w.write_all(&self.section_alignment.to_le_bytes())?;
        w.write_all(&self.file_alignment.to_le_bytes())?;
        w.write_all(&self.major_os_version.to_le_bytes())?;
        w.write_all(&self.minor_os_version.to_le_bytes())?;
        w.write_all(&self.major_image_version.to_le_bytes())?;
        w.write_all(&self.minor_image_version.to_le_bytes())?;
        w.write_all(&self.major_subsystem_version.to_le_bytes())?;
        w.write_all(&self.minor_subsystem_version.to_le_bytes())?;
        w.write_all(&self.win32_version_value.to_le_bytes())?;
        w.write_all(&self.size_of_image.to_le_bytes())?;
        w.write_all(&self.size_of_headers.to_le_bytes())?;
        w.write_all(&self.checksum.to_le_bytes())?;
        w.write_all(&self.subsystem.to_le_bytes())?;
        w.write_all(&self.dll_characteristics.to_le_bytes())?;
        w.write_all(&self.size_of_stack_reserve.to_le_bytes())?;
        w.write_all(&self.size_of_stack_commit.to_le_bytes())?;
        w.write_all(&self.size_of_heap_reserve.to_le_bytes())?;
        w.write_all(&self.size_of_heap_commit.to_le_bytes())?;
        w.write_all(&self.loader_flags.to_le_bytes())?;
        w.write_all(&self.number_of_rva_and_sizes.to_le_bytes())?;

        for dd in &self.data_directories {
            dd.write(w)?;
        }

        Ok(())
    }
}

/// Section Header (40 bytes)
#[derive(Debug, Clone)]
pub struct SectionHeader {
    pub name: [u8; 8],
    pub virtual_size: u32,
    pub virtual_address: u32,
    pub size_of_raw_data: u32,
    pub pointer_to_raw_data: u32,
    pub pointer_to_relocations: u32,
    pub pointer_to_linenumbers: u32,
    pub number_of_relocations: u16,
    pub number_of_linenumbers: u16,
    pub characteristics: u32,
}

impl SectionHeader {
    pub fn new(name: &str, characteristics: u32) -> Self {
        let mut name_bytes = [0u8; 8];
        let bytes = name.as_bytes();
        let len = bytes.len().min(8);
        name_bytes[..len].copy_from_slice(&bytes[..len]);

        Self {
            name: name_bytes,
            virtual_size: 0,
            virtual_address: 0,
            size_of_raw_data: 0,
            pointer_to_raw_data: 0,
            pointer_to_relocations: 0,
            pointer_to_linenumbers: 0,
            number_of_relocations: 0,
            number_of_linenumbers: 0,
            characteristics,
        }
    }

    pub fn write<W: Write>(&self, w: &mut W) -> io::Result<()> {
        w.write_all(&self.name)?;
        w.write_all(&self.virtual_size.to_le_bytes())?;
        w.write_all(&self.virtual_address.to_le_bytes())?;
        w.write_all(&self.size_of_raw_data.to_le_bytes())?;
        w.write_all(&self.pointer_to_raw_data.to_le_bytes())?;
        w.write_all(&self.pointer_to_relocations.to_le_bytes())?;
        w.write_all(&self.pointer_to_linenumbers.to_le_bytes())?;
        w.write_all(&self.number_of_relocations.to_le_bytes())?;
        w.write_all(&self.number_of_linenumbers.to_le_bytes())?;
        w.write_all(&self.characteristics.to_le_bytes())?;
        Ok(())
    }
}

/// Import directory entry
#[derive(Debug, Clone, Default)]
pub struct ImportDirectoryEntry {
    pub import_lookup_table_rva: u32,
    pub time_date_stamp: u32,
    pub forwarder_chain: u32,
    pub name_rva: u32,
    pub import_address_table_rva: u32,
}

impl ImportDirectoryEntry {
    pub fn write<W: Write>(&self, w: &mut W) -> io::Result<()> {
        w.write_all(&self.import_lookup_table_rva.to_le_bytes())?;
        w.write_all(&self.time_date_stamp.to_le_bytes())?;
        w.write_all(&self.forwarder_chain.to_le_bytes())?;
        w.write_all(&self.name_rva.to_le_bytes())?;
        w.write_all(&self.import_address_table_rva.to_le_bytes())?;
        Ok(())
    }
}

/// PE32+ executable builder for Windows x64
#[derive(Debug)]
pub struct Pe64Builder {
    image_base: u64,
    code: Vec<u8>,
}

impl Pe64Builder {
    pub fn new() -> Self {
        Self {
            image_base: consts::DEFAULT_IMAGE_BASE,
            code: Vec::new(),
        }
    }

    /// Set the image base address
    pub fn image_base(mut self, addr: u64) -> Self {
        self.image_base = addr;
        self
    }

    /// Set the executable code
    pub fn code(mut self, code: Vec<u8>) -> Self {
        self.code = code;
        self
    }

    /// Align value up to alignment boundary
    fn align_up(value: u32, alignment: u32) -> u32 {
        (value + alignment - 1) & !(alignment - 1)
    }

    /// Build the complete PE file with imports for kernel32.dll
    pub fn build(self) -> Vec<u8> {
        // Layout calculation
        // PE header starts right after DOS header (offset 64)
        let pe_header_offset: u32 = consts::DOS_HEADER_SIZE as u32;

        // Headers: DOS + PE sig + COFF + Optional + 2 section headers
        let num_sections: u16 = 2; // .text and .idata
        let headers_size = consts::DOS_HEADER_SIZE
            + 4 // PE signature
            + consts::COFF_HEADER_SIZE
            + consts::OPTIONAL_HEADER_SIZE
            + (consts::SECTION_HEADER_SIZE * num_sections as usize);

        let headers_aligned = Self::align_up(headers_size as u32, consts::FILE_ALIGNMENT);

        // .text section (code)
        let text_file_offset = headers_aligned;
        let text_rva: u32 = consts::SECTION_ALIGNMENT; // 0x1000
        let text_size = self.code.len() as u32;
        let text_size_aligned = Self::align_up(text_size, consts::FILE_ALIGNMENT);

        // .idata section (imports)
        let idata_file_offset = text_file_offset + text_size_aligned;
        let idata_rva = text_rva + Self::align_up(text_size, consts::SECTION_ALIGNMENT);

        // Import data layout within .idata:
        // - Import Directory Table (2 entries * 20 bytes = 40 bytes, null terminated)
        // - Import Lookup Table (3 entries * 8 bytes = 24 bytes, null terminated)
        // - Import Address Table (same as ILT, 24 bytes)
        // - Hint/Name Table (function names with 2-byte hints)
        // - DLL name strings

        // Function names we need:
        // "GetStdHandle" (12 chars)
        // "WriteFile" (9 chars)
        // "ExitProcess" (11 chars)

        let import_dir_size = 40; // 2 entries (1 real + 1 null terminator)
        let ilt_offset = import_dir_size;
        let ilt_size = 32; // 4 entries * 8 bytes (3 functions + null)
        let iat_offset = ilt_offset + ilt_size;
        let iat_size = ilt_size; // Same structure as ILT

        // Hint/Name table
        let hint_name_offset = iat_offset + iat_size;
        // Each entry: 2-byte hint + null-terminated name + padding to 2-byte boundary
        let get_std_handle_entry_size = 2 + 13; // "GetStdHandle\0" = 13 bytes, padded
        let write_file_entry_size = 2 + 10; // "WriteFile\0" = 10 bytes
        let exit_process_entry_size = 2 + 12; // "ExitProcess\0" = 12 bytes
        let hint_name_size = Self::align_up(
            (get_std_handle_entry_size + write_file_entry_size + exit_process_entry_size) as u32,
            2,
        );

        // DLL name
        let dll_name_offset = hint_name_offset + hint_name_size as usize;
        let dll_name = b"kernel32.dll\0";
        let dll_name_size = dll_name.len();

        let idata_size = (dll_name_offset + dll_name_size) as u32;
        let idata_size_aligned = Self::align_up(idata_size, consts::FILE_ALIGNMENT);

        // Total image size
        let size_of_image = idata_rva + Self::align_up(idata_size, consts::SECTION_ALIGNMENT);

        // Build import data
        let mut idata = vec![0u8; idata_size as usize];

        // Calculate RVAs for import structures
        let ilt_rva = idata_rva + ilt_offset as u32;
        let iat_rva = idata_rva + iat_offset as u32;
        let hint_name_rva = idata_rva + hint_name_offset as u32;
        let dll_name_rva = idata_rva + dll_name_offset as u32;

        // Import Directory Entry for kernel32.dll
        let import_dir = ImportDirectoryEntry {
            import_lookup_table_rva: ilt_rva,
            time_date_stamp: 0,
            forwarder_chain: 0,
            name_rva: dll_name_rva,
            import_address_table_rva: iat_rva,
        };

        // Write import directory
        let mut cursor = std::io::Cursor::new(&mut idata[..]);
        import_dir.write(&mut cursor).unwrap();
        // Null terminator entry (20 bytes of zeros) - already zero

        // Hint/Name Table entries' RVAs
        let get_std_handle_rva = hint_name_rva;
        let write_file_rva = hint_name_rva + get_std_handle_entry_size as u32;
        let exit_process_rva = write_file_rva + write_file_entry_size as u32;

        // Write ILT (Import Lookup Table)
        let ilt_entries = [
            get_std_handle_rva as u64,
            write_file_rva as u64,
            exit_process_rva as u64,
            0u64, // null terminator
        ];
        for (i, &entry) in ilt_entries.iter().enumerate() {
            let offset = ilt_offset + i * 8;
            idata[offset..offset + 8].copy_from_slice(&entry.to_le_bytes());
        }

        // Write IAT (Import Address Table) - same as ILT initially
        for (i, &entry) in ilt_entries.iter().enumerate() {
            let offset = iat_offset + i * 8;
            idata[offset..offset + 8].copy_from_slice(&entry.to_le_bytes());
        }

        // Write Hint/Name Table
        let mut offset = hint_name_offset;

        // GetStdHandle (hint 0)
        idata[offset] = 0;
        idata[offset + 1] = 0;
        let name = b"GetStdHandle\0";
        idata[offset + 2..offset + 2 + name.len()].copy_from_slice(name);
        offset += get_std_handle_entry_size;

        // WriteFile (hint 0)
        idata[offset] = 0;
        idata[offset + 1] = 0;
        let name = b"WriteFile\0";
        idata[offset + 2..offset + 2 + name.len()].copy_from_slice(name);
        offset += write_file_entry_size;

        // ExitProcess (hint 0)
        idata[offset] = 0;
        idata[offset + 1] = 0;
        let name = b"ExitProcess\0";
        idata[offset + 2..offset + 2 + name.len()].copy_from_slice(name);

        // Write DLL name
        idata[dll_name_offset..dll_name_offset + dll_name.len()].copy_from_slice(dll_name);

        // Create headers
        let dos_header = DosHeader::new(pe_header_offset);
        let coff_header = CoffHeader::new(num_sections);

        let mut optional_header = OptionalHeader::default();
        optional_header.image_base = self.image_base;
        optional_header.address_of_entry_point = text_rva; // Entry at start of .text
        optional_header.base_of_code = text_rva;
        optional_header.size_of_code = text_size_aligned;
        optional_header.size_of_initialized_data = idata_size_aligned;
        optional_header.size_of_image = size_of_image;
        optional_header.size_of_headers = headers_aligned;

        // Set data directories
        optional_header.data_directories[consts::IMAGE_DIRECTORY_ENTRY_IMPORT] = DataDirectory {
            virtual_address: idata_rva,
            size: import_dir_size as u32,
        };
        optional_header.data_directories[consts::IMAGE_DIRECTORY_ENTRY_IAT] = DataDirectory {
            virtual_address: iat_rva,
            size: iat_size as u32,
        };

        // Create section headers
        let mut text_section = SectionHeader::new(
            ".text",
            consts::IMAGE_SCN_CNT_CODE | consts::IMAGE_SCN_MEM_EXECUTE | consts::IMAGE_SCN_MEM_READ,
        );
        text_section.virtual_size = text_size;
        text_section.virtual_address = text_rva;
        text_section.size_of_raw_data = text_size_aligned;
        text_section.pointer_to_raw_data = text_file_offset;

        let mut idata_section = SectionHeader::new(
            ".idata",
            consts::IMAGE_SCN_CNT_INITIALIZED_DATA
                | consts::IMAGE_SCN_MEM_READ
                | consts::IMAGE_SCN_MEM_WRITE,
        );
        idata_section.virtual_size = idata_size;
        idata_section.virtual_address = idata_rva;
        idata_section.size_of_raw_data = idata_size_aligned;
        idata_section.pointer_to_raw_data = idata_file_offset;

        // Build the PE file
        let total_file_size = (idata_file_offset + idata_size_aligned) as usize;
        let mut pe = vec![0u8; total_file_size];

        // Write DOS header
        let mut cursor = std::io::Cursor::new(&mut pe[..]);
        dos_header.write(&mut cursor).unwrap();

        // Write PE signature
        cursor.set_position(pe_header_offset as u64);
        cursor
            .write_all(&consts::PE_SIGNATURE.to_le_bytes())
            .unwrap();

        // Write COFF header
        coff_header.write(&mut cursor).unwrap();

        // Write Optional header
        optional_header.write(&mut cursor).unwrap();

        // Write section headers
        text_section.write(&mut cursor).unwrap();
        idata_section.write(&mut cursor).unwrap();

        // Write .text section (code)
        pe[text_file_offset as usize..text_file_offset as usize + self.code.len()]
            .copy_from_slice(&self.code);

        // Write .idata section (imports)
        pe[idata_file_offset as usize..idata_file_offset as usize + idata.len()]
            .copy_from_slice(&idata);

        pe
    }

    /// Get the RVA where IAT entries will be located
    /// Returns (GetStdHandle_iat, WriteFile_iat, ExitProcess_iat)
    pub fn get_iat_rvas(&self) -> (u32, u32, u32) {
        Self::calculate_iat_rvas(self.code.len() as u32)
    }

    /// Calculate IAT RVAs for a given code size
    /// This can be used before code is generated to estimate positions
    /// Returns (GetStdHandle_iat, WriteFile_iat, ExitProcess_iat)
    pub fn calculate_iat_rvas(code_size: u32) -> (u32, u32, u32) {
        // Based on the layout in build():
        let text_size_aligned = Self::align_up(code_size, consts::SECTION_ALIGNMENT);
        let idata_rva = consts::SECTION_ALIGNMENT + text_size_aligned;

        let import_dir_size = 40;
        let ilt_size = 32;
        let iat_offset = import_dir_size + ilt_size;
        let iat_rva = idata_rva + iat_offset as u32;

        (iat_rva, iat_rva + 8, iat_rva + 16)
    }

    /// Calculate IAT RVAs assuming code fits in one page (< 4KB)
    /// Use this for small programs
    pub fn calculate_iat_rvas_small() -> (u32, u32, u32) {
        // Assume code < 0x1000, so idata starts at 0x2000
        let idata_rva = 0x2000u32;

        let import_dir_size = 40;
        let ilt_size = 32;
        let iat_offset = import_dir_size + ilt_size;
        let iat_rva = idata_rva + iat_offset as u32;

        (iat_rva, iat_rva + 8, iat_rva + 16)
    }

    /// Write to file
    pub fn write_to_file(self, path: &std::path::Path) -> io::Result<()> {
        use std::fs::File;

        let data = self.build();
        let mut file = File::create(path)?;
        file.write_all(&data)?;
        Ok(())
    }
}

impl Default for Pe64Builder {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_dos_header_size() {
        let header = DosHeader::new(64);
        let mut buf = Vec::new();
        header.write(&mut buf).unwrap();
        assert_eq!(buf.len(), 64);
    }

    #[test]
    fn test_coff_header_size() {
        let header = CoffHeader::new(2);
        let mut buf = Vec::new();
        header.write(&mut buf).unwrap();
        assert_eq!(buf.len(), 20);
    }

    #[test]
    fn test_optional_header_size() {
        let header = OptionalHeader::default();
        let mut buf = Vec::new();
        header.write(&mut buf).unwrap();
        assert_eq!(buf.len(), 240);
    }

    #[test]
    fn test_section_header_size() {
        let header = SectionHeader::new(".text", 0);
        let mut buf = Vec::new();
        header.write(&mut buf).unwrap();
        assert_eq!(buf.len(), 40);
    }

    #[test]
    fn test_pe_magic() {
        let builder = Pe64Builder::new().code(vec![0xC3]); // ret
        let pe = builder.build();

        // Check DOS magic (MZ)
        assert_eq!(&pe[0..2], &[0x4D, 0x5A]);

        // Check PE signature at offset 64
        assert_eq!(&pe[64..68], &[0x50, 0x45, 0x00, 0x00]); // "PE\0\0"
    }

    #[test]
    fn test_pe_machine() {
        let builder = Pe64Builder::new().code(vec![0xC3]);
        let pe = builder.build();

        // Machine type at offset 64+4 = 68
        let machine = u16::from_le_bytes([pe[68], pe[69]]);
        assert_eq!(machine, consts::IMAGE_FILE_MACHINE_AMD64);
    }
}
