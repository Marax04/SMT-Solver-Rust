//! Pure Rust ELF64 and PE32+ (PE64) binary loader and machine code extractor.
//!
//! Parses executable headers, enumerates sections (.text, .rodata, etc.),
//! resolves virtual memory addresses (RVAs) to file offsets, and extracts
//! entry point instructions for symbolic execution and SMT analysis.

/// Parsed section representation within an ELF64 binary.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Elf64Section {
    pub name: String,
    pub sh_type: u32,
    pub sh_flags: u64,
    pub sh_addr: u64,
    pub sh_offset: u64,
    pub sh_size: u64,
}

/// Parsed ELF64 file header and section table.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Elf64File {
    pub entry_point: u64,
    pub sections: Vec<Elf64Section>,
}

impl Elf64File {
    /// Parses an ELF64 binary from raw file bytes.
    pub fn parse(bytes: &[u8]) -> Result<Self, String> {
        if bytes.len() < 64 {
            return Err("File too small for ELF64 header (< 64 bytes)".to_string());
        }

        // Check magic: 0x7F, 'E', 'L', 'F'
        if &bytes[0..4] != b"\x7fELF" {
            return Err("Invalid ELF magic header".to_string());
        }

        // EI_CLASS must be 2 (64-bit)
        if bytes[4] != 2 {
            return Err(format!(
                "Unsupported ELF class: expected 2 (64-bit), got {}",
                bytes[4]
            ));
        }

        // EI_DATA must be 1 (little-endian)
        if bytes[5] != 1 {
            return Err(format!(
                "Unsupported ELF endianness: expected 1 (little-endian), got {}",
                bytes[5]
            ));
        }

        // e_machine at offset 18 must be 0x3E (AMD x86-64)
        let e_machine = u16::from_le_bytes([bytes[18], bytes[19]]);
        if e_machine != 0x3e {
            return Err(format!(
                "Unsupported ELF machine architecture: 0x{:04x} (expected 0x003e for x86-64)",
                e_machine
            ));
        }

        // e_entry at offset 24 (8 bytes)
        let entry_point = u64::from_le_bytes([
            bytes[24], bytes[25], bytes[26], bytes[27], bytes[28], bytes[29], bytes[30], bytes[31],
        ]);

        // e_shoff at offset 40 (8 bytes)
        let e_shoff = u64::from_le_bytes([
            bytes[40], bytes[41], bytes[42], bytes[43], bytes[44], bytes[45], bytes[46], bytes[47],
        ]) as usize;

        // e_shentsize at offset 58 (2 bytes), e_shnum at offset 60 (2 bytes)
        let e_shentsize = u16::from_le_bytes([bytes[58], bytes[59]]) as usize;
        let e_shnum = u16::from_le_bytes([bytes[60], bytes[61]]) as usize;
        let e_shstrndx = u16::from_le_bytes([bytes[62], bytes[63]]) as usize;

        if e_shoff == 0 || e_shnum == 0 || e_shentsize < 64 {
            return Ok(Elf64File {
                entry_point,
                sections: Vec::new(),
            });
        }

        if e_shoff + e_shnum * e_shentsize > bytes.len() {
            return Err("Section header table extends beyond file boundaries".to_string());
        }

        struct RawShdr {
            name_offset: u32,
            sh_type: u32,
            sh_flags: u64,
            sh_addr: u64,
            sh_offset: u64,
            sh_size: u64,
        }

        let mut raw_shdrs = Vec::with_capacity(e_shnum);
        for i in 0..e_shnum {
            let offset = e_shoff + i * e_shentsize;
            let sh_name = u32::from_le_bytes([
                bytes[offset],
                bytes[offset + 1],
                bytes[offset + 2],
                bytes[offset + 3],
            ]);
            let sh_type = u32::from_le_bytes([
                bytes[offset + 4],
                bytes[offset + 5],
                bytes[offset + 6],
                bytes[offset + 7],
            ]);
            let sh_flags = u64::from_le_bytes([
                bytes[offset + 8],
                bytes[offset + 9],
                bytes[offset + 10],
                bytes[offset + 11],
                bytes[offset + 12],
                bytes[offset + 13],
                bytes[offset + 14],
                bytes[offset + 15],
            ]);
            let sh_addr = u64::from_le_bytes([
                bytes[offset + 16],
                bytes[offset + 17],
                bytes[offset + 18],
                bytes[offset + 19],
                bytes[offset + 20],
                bytes[offset + 21],
                bytes[offset + 22],
                bytes[offset + 23],
            ]);
            let sh_file_offset = u64::from_le_bytes([
                bytes[offset + 24],
                bytes[offset + 25],
                bytes[offset + 26],
                bytes[offset + 27],
                bytes[offset + 28],
                bytes[offset + 29],
                bytes[offset + 30],
                bytes[offset + 31],
            ]);
            let sh_size = u64::from_le_bytes([
                bytes[offset + 32],
                bytes[offset + 33],
                bytes[offset + 34],
                bytes[offset + 35],
                bytes[offset + 36],
                bytes[offset + 37],
                bytes[offset + 38],
                bytes[offset + 39],
            ]);

            raw_shdrs.push(RawShdr {
                name_offset: sh_name,
                sh_type,
                sh_flags,
                sh_addr,
                sh_offset: sh_file_offset,
                sh_size,
            });
        }

        let strtab_bytes = if e_shstrndx < raw_shdrs.len() {
            let str_hdr = &raw_shdrs[e_shstrndx];
            let start = str_hdr.sh_offset as usize;
            let end = start + str_hdr.sh_size as usize;
            if end <= bytes.len() {
                &bytes[start..end]
            } else {
                &[]
            }
        } else {
            &[]
        };

        let mut sections = Vec::with_capacity(e_shnum);
        for raw in raw_shdrs {
            let name = if (raw.name_offset as usize) < strtab_bytes.len() {
                let name_slice = &strtab_bytes[raw.name_offset as usize..];
                let null_pos = name_slice
                    .iter()
                    .position(|&b| b == 0)
                    .unwrap_or(name_slice.len());
                String::from_utf8_lossy(&name_slice[..null_pos]).to_string()
            } else {
                format!("sec_{}", sections.len())
            };

            sections.push(Elf64Section {
                name,
                sh_type: raw.sh_type,
                sh_flags: raw.sh_flags,
                sh_addr: raw.sh_addr,
                sh_offset: raw.sh_offset,
                sh_size: raw.sh_size,
            });
        }

        Ok(Elf64File {
            entry_point,
            sections,
        })
    }

    /// Finds a section by name (e.g. ".text", ".rodata").
    pub fn find_section(&self, name: &str) -> Option<&Elf64Section> {
        self.sections.iter().find(|s| s.name == name)
    }

    /// Extracts machine code bytes starting at the entry point.
    pub fn extract_entry_point_bytes<'a>(
        &self,
        raw: &'a [u8],
        max_len: usize,
    ) -> Result<&'a [u8], String> {
        for sec in &self.sections {
            if self.entry_point >= sec.sh_addr && self.entry_point < sec.sh_addr + sec.sh_size {
                let offset_in_sec = (self.entry_point - sec.sh_addr) as usize;
                let file_start = sec.sh_offset as usize + offset_in_sec;
                let avail = (sec.sh_size as usize).saturating_sub(offset_in_sec);
                let len = avail.min(max_len);
                if file_start + len <= raw.len() {
                    return Ok(&raw[file_start..file_start + len]);
                }
            }
        }

        if let Some(text_sec) = self.find_section(".text") {
            let start = text_sec.sh_offset as usize;
            let len = (text_sec.sh_size as usize).min(max_len);
            if start + len <= raw.len() {
                return Ok(&raw[start..start + len]);
            }
        }

        Err("Could not locate entry point machine code in ELF sections".to_string())
    }
}

/// Parsed section representation within a PE32+ binary.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PeSection {
    pub name: String,
    pub virtual_size: u32,
    pub virtual_address: u32,
    pub size_of_raw_data: u32,
    pub pointer_to_raw_data: u32,
}

/// Parsed PE32+ (x86-64) binary structure.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Pe64File {
    pub entry_point_rva: u32,
    pub image_base: u64,
    pub sections: Vec<PeSection>,
}

impl Pe64File {
    /// Parses a PE32+ (64-bit) binary from raw bytes.
    pub fn parse(bytes: &[u8]) -> Result<Self, String> {
        if bytes.len() < 0x40 {
            return Err("File too small for DOS header (< 64 bytes)".to_string());
        }

        if &bytes[0..2] != b"MZ" {
            return Err("Invalid DOS signature: expected 'MZ'".to_string());
        }

        let pe_offset =
            u32::from_le_bytes([bytes[0x3c], bytes[0x3d], bytes[0x3e], bytes[0x3f]]) as usize;
        if pe_offset + 24 > bytes.len() {
            return Err("PE header offset out of bounds".to_string());
        }

        if &bytes[pe_offset..pe_offset + 4] != b"PE\0\0" {
            return Err("Invalid PE signature".to_string());
        }

        let coff_offset = pe_offset + 4;
        let machine = u16::from_le_bytes([bytes[coff_offset], bytes[coff_offset + 1]]);
        if machine != 0x8664 {
            return Err(format!(
                "Unsupported PE Machine: 0x{:04x} (expected 0x8664 for x86-64)",
                machine
            ));
        }

        let num_sections =
            u16::from_le_bytes([bytes[coff_offset + 2], bytes[coff_offset + 3]]) as usize;
        let opt_hdr_size =
            u16::from_le_bytes([bytes[coff_offset + 16], bytes[coff_offset + 17]]) as usize;

        let opt_offset = coff_offset + 20;
        if opt_offset + opt_hdr_size > bytes.len() || opt_hdr_size < 112 {
            return Err("Optional header truncated or missing".to_string());
        }

        let opt_magic = u16::from_le_bytes([bytes[opt_offset], bytes[opt_offset + 1]]);
        if opt_magic != 0x020b {
            return Err(format!(
                "Unsupported Optional Header magic: 0x{:04x} (expected 0x020B for PE32+)",
                opt_magic
            ));
        }

        let entry_point_rva = u32::from_le_bytes([
            bytes[opt_offset + 16],
            bytes[opt_offset + 17],
            bytes[opt_offset + 18],
            bytes[opt_offset + 19],
        ]);

        let image_base = u64::from_le_bytes([
            bytes[opt_offset + 24],
            bytes[opt_offset + 25],
            bytes[opt_offset + 26],
            bytes[opt_offset + 27],
            bytes[opt_offset + 28],
            bytes[opt_offset + 29],
            bytes[opt_offset + 30],
            bytes[opt_offset + 31],
        ]);

        let sec_table_offset = opt_offset + opt_hdr_size;
        let sec_entry_size = 40;
        if sec_table_offset + num_sections * sec_entry_size > bytes.len() {
            return Err("Section table out of bounds".to_string());
        }

        let mut sections = Vec::with_capacity(num_sections);
        for i in 0..num_sections {
            let offset = sec_table_offset + i * sec_entry_size;
            let name_slice = &bytes[offset..offset + 8];
            let null_pos = name_slice.iter().position(|&b| b == 0).unwrap_or(8);
            let name = String::from_utf8_lossy(&name_slice[..null_pos]).to_string();

            let virtual_size = u32::from_le_bytes([
                bytes[offset + 8],
                bytes[offset + 9],
                bytes[offset + 10],
                bytes[offset + 11],
            ]);
            let virtual_address = u32::from_le_bytes([
                bytes[offset + 12],
                bytes[offset + 13],
                bytes[offset + 14],
                bytes[offset + 15],
            ]);
            let size_of_raw_data = u32::from_le_bytes([
                bytes[offset + 16],
                bytes[offset + 17],
                bytes[offset + 18],
                bytes[offset + 19],
            ]);
            let pointer_to_raw_data = u32::from_le_bytes([
                bytes[offset + 20],
                bytes[offset + 21],
                bytes[offset + 22],
                bytes[offset + 23],
            ]);

            sections.push(PeSection {
                name,
                virtual_size,
                virtual_address,
                size_of_raw_data,
                pointer_to_raw_data,
            });
        }

        Ok(Pe64File {
            entry_point_rva,
            image_base,
            sections,
        })
    }

    /// Converts an RVA to a physical file offset.
    pub fn rva_to_file_offset(&self, rva: u32) -> Option<usize> {
        for sec in &self.sections {
            let span = sec.virtual_size.max(sec.size_of_raw_data);
            if rva >= sec.virtual_address && rva < sec.virtual_address + span {
                let off_in_sec = rva - sec.virtual_address;
                return Some((sec.pointer_to_raw_data + off_in_sec) as usize);
            }
        }
        None
    }

    /// Extracts entry point machine code bytes from raw PE file bytes.
    pub fn extract_entry_point_bytes<'a>(
        &self,
        raw: &'a [u8],
        max_len: usize,
    ) -> Result<&'a [u8], String> {
        if let Some(file_offset) = self.rva_to_file_offset(self.entry_point_rva) {
            let avail = raw.len().saturating_sub(file_offset);
            let len = avail.min(max_len);
            if len > 0 {
                return Ok(&raw[file_offset..file_offset + len]);
            }
        }

        if let Some(text_sec) = self.sections.iter().find(|s| s.name == ".text") {
            let start = text_sec.pointer_to_raw_data as usize;
            let len = (text_sec.size_of_raw_data as usize).min(max_len);
            if start + len <= raw.len() {
                return Ok(&raw[start..start + len]);
            }
        }

        Err("Could not resolve entry point RVA to file offset in PE sections".to_string())
    }
}

/// Unified binary format classifier.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum BinaryFormat {
    Elf64(Elf64File),
    Pe64(Pe64File),
    RawMachineCode,
}

/// High-level loader detecting and extracting executable code.
pub struct BinaryLoader;

impl BinaryLoader {
    /// Detects format (ELF64, PE64, or raw machine code) and extracts the target code buffer.
    pub fn detect_and_extract(bytes: &[u8]) -> (BinaryFormat, &[u8], u64) {
        if bytes.len() >= 4 && &bytes[0..4] == b"\x7fELF" {
            if let Ok(elf) = Elf64File::parse(bytes) {
                if let Ok(code) = elf.extract_entry_point_bytes(bytes, 4096) {
                    let ep = elf.entry_point;
                    return (BinaryFormat::Elf64(elf), code, ep);
                }
            }
        }

        if bytes.len() >= 2 && &bytes[0..2] == b"MZ" {
            if let Ok(pe) = Pe64File::parse(bytes) {
                if let Ok(code) = pe.extract_entry_point_bytes(bytes, 4096) {
                    let ep = pe.image_base + pe.entry_point_rva as u64;
                    return (BinaryFormat::Pe64(pe), code, ep);
                }
            }
        }

        (BinaryFormat::RawMachineCode, bytes, 0x1000)
    }
}
