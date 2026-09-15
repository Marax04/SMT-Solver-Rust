//! Pure Rust ELF64 and PE32+ (PE64) binary loader and machine code extractor.
//!
//! Hardened for analysis of untrusted binaries: uses checked arithmetic throughout,
//! enforces strict resource limits against adversarial denial-of-service inputs,
//! validates ELF segment view (`PT_LOAD`, permissions, BSS, PIE load bias),
//! parses PE32+ runtime models (Data Directories, IAT/Imports, Base Relocations, TLS),
//! and maps executables into a structured virtual address space (`LoadedProcessImage`).

use std::fmt;

/// Maximum allowed section headers to prevent resource exhaustion attacks.
pub const MAX_SECTIONS: usize = 512;

/// Maximum allowed ELF program headers to prevent resource exhaustion attacks.
pub const MAX_PROGRAM_HEADERS: usize = 256;

/// Maximum allowed virtual memory footprint per loaded binary image (512 MB).
pub const MAX_IMAGE_SIZE: usize = 512 * 1024 * 1024;

/// Maximum allowed base relocation entries.
pub const MAX_RELOCATIONS: usize = 65536;

/// Maximum allowed import table entries.
pub const MAX_IMPORTS: usize = 4096;

/// Structured, non-panicking error conditions for binary parsing and loading.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum LoaderError {
    FileTooSmall {
        expected: usize,
        actual: usize,
    },
    InvalidMagic(String),
    UnsupportedArchitecture(String),
    IntegerOverflow(String),
    OutOfBounds {
        offset: usize,
        size: usize,
        file_len: usize,
    },
    MalformedHeader(String),
    ResourceLimitExceeded {
        resource: String,
        count: usize,
        limit: usize,
    },
    AlignmentViolation {
        vaddr: u64,
        offset: u64,
        align: u64,
    },
    EntryPointOutsideSegments {
        entry_point: u64,
    },
    RelocationError(String),
    ImportError(String),
    MemoryPermissionViolation {
        vaddr: u64,
        attempted: &'static str,
    },
}

impl fmt::Display for LoaderError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::FileTooSmall { expected, actual } => {
                write!(
                    f,
                    "File too small: expected >= {} bytes, got {} bytes",
                    expected, actual
                )
            }
            Self::InvalidMagic(msg) => write!(f, "Invalid magic signature: {}", msg),
            Self::UnsupportedArchitecture(msg) => write!(f, "Unsupported architecture: {}", msg),
            Self::IntegerOverflow(msg) => {
                write!(f, "Integer overflow in header calculation: {}", msg)
            }
            Self::OutOfBounds {
                offset,
                size,
                file_len,
            } => {
                write!(
                    f,
                    "Offset {:#x} + size {:#x} extends beyond file length {:#x}",
                    offset, size, file_len
                )
            }
            Self::MalformedHeader(msg) => write!(f, "Malformed header structure: {}", msg),
            Self::ResourceLimitExceeded {
                resource,
                count,
                limit,
            } => {
                write!(
                    f,
                    "Resource limit exceeded for {}: count {} > limit {}",
                    resource, count, limit
                )
            }
            Self::AlignmentViolation {
                vaddr,
                offset,
                align,
            } => {
                write!(
                    f,
                    "Alignment congruence violated: vaddr {:#x} % {:#x} != offset {:#x} % {:#x}",
                    vaddr, align, offset, align
                )
            }
            Self::EntryPointOutsideSegments { entry_point } => {
                write!(
                    f,
                    "Entry point {:#x} is outside any mapped executable segment",
                    entry_point
                )
            }
            Self::RelocationError(msg) => write!(f, "Relocation processing error: {}", msg),
            Self::ImportError(msg) => write!(f, "Import processing error: {}", msg),
            Self::MemoryPermissionViolation { vaddr, attempted } => {
                write!(
                    f,
                    "Memory permission violation at {:#x}: cannot perform {}",
                    vaddr, attempted
                )
            }
        }
    }
}

impl std::error::Error for LoaderError {}

// -----------------------------------------------------------------------------
// ELF64 Program Header & Section Structures
// -----------------------------------------------------------------------------

/// ELF Segment / Program Header Type constants.
pub const PT_NULL: u32 = 0;
pub const PT_LOAD: u32 = 1;
pub const PT_DYNAMIC: u32 = 2;
pub const PT_INTERP: u32 = 3;
pub const PT_NOTE: u32 = 4;
pub const PT_SHLIB: u32 = 5;
pub const PT_PHDR: u32 = 6;
pub const PT_TLS: u32 = 7;
pub const PT_GNU_STACK: u32 = 0x6474e551;
pub const PT_GNU_RELRO: u32 = 0x6474e552;

/// ELF Segment Permission Flags.
pub const PF_X: u32 = 1; // Execute
pub const PF_W: u32 = 2; // Write
pub const PF_R: u32 = 4; // Read

/// Parsed program header (segment) within an ELF64 binary.
#[derive(Debug, Clone, PartialEq, Eq)]
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
    #[inline]
    pub fn is_load(&self) -> bool {
        self.p_type == PT_LOAD
    }

    #[inline]
    pub fn is_executable(&self) -> bool {
        (self.p_flags & PF_X) != 0
    }

    #[inline]
    pub fn is_writable(&self) -> bool {
        (self.p_flags & PF_W) != 0
    }

    #[inline]
    pub fn is_readable(&self) -> bool {
        (self.p_flags & PF_R) != 0
    }
}

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

impl Elf64Section {
    #[inline]
    pub fn is_writable(&self) -> bool {
        (self.sh_flags & 0x1) != 0
    }

    #[inline]
    pub fn is_alloc(&self) -> bool {
        (self.sh_flags & 0x2) != 0
    }

    #[inline]
    pub fn is_executable(&self) -> bool {
        (self.sh_flags & 0x4) != 0
    }
}

/// Parsed ELF64 file header, program headers (runtime segment view), and section table.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Elf64File {
    pub elf_type: u16,
    pub entry_point: u64,
    pub program_headers: Vec<Elf64ProgramHeader>,
    pub sections: Vec<Elf64Section>,
}

impl Elf64File {
    /// Parses an ELF64 binary from raw file bytes with checked arithmetic and resource limits.
    pub fn parse(bytes: &[u8]) -> Result<Self, LoaderError> {
        if bytes.len() < 64 {
            return Err(LoaderError::FileTooSmall {
                expected: 64,
                actual: bytes.len(),
            });
        }

        // Check magic: 0x7F, 'E', 'L', 'F'
        if &bytes[0..4] != b"\x7fELF" {
            return Err(LoaderError::InvalidMagic("Expected \\x7fELF".to_string()));
        }

        // EI_CLASS must be 2 (64-bit)
        if bytes[4] != 2 {
            return Err(LoaderError::UnsupportedArchitecture(format!(
                "Expected 64-bit ELF class 2, got {}",
                bytes[4]
            )));
        }

        // EI_DATA must be 1 (little-endian)
        if bytes[5] != 1 {
            return Err(LoaderError::UnsupportedArchitecture(format!(
                "Expected little-endian ELF data 1, got {}",
                bytes[5]
            )));
        }

        // e_type at offset 16 (2 bytes)
        let elf_type = u16::from_le_bytes([bytes[16], bytes[17]]);

        // e_machine at offset 18 must be 0x3E (AMD x86-64)
        let e_machine = u16::from_le_bytes([bytes[18], bytes[19]]);
        if e_machine != 0x3e {
            return Err(LoaderError::UnsupportedArchitecture(format!(
                "Architecture 0x{:04x} is not AMD x86-64 (0x003e)",
                e_machine
            )));
        }

        // e_entry at offset 24 (8 bytes)
        let entry_point = u64::from_le_bytes([
            bytes[24], bytes[25], bytes[26], bytes[27], bytes[28], bytes[29], bytes[30], bytes[31],
        ]);

        // e_phoff at offset 32 (8 bytes)
        let e_phoff = u64::from_le_bytes([
            bytes[32], bytes[33], bytes[34], bytes[35], bytes[36], bytes[37], bytes[38], bytes[39],
        ]) as usize;

        // e_shoff at offset 40 (8 bytes)
        let e_shoff = u64::from_le_bytes([
            bytes[40], bytes[41], bytes[42], bytes[43], bytes[44], bytes[45], bytes[46], bytes[47],
        ]) as usize;

        // e_phentsize at offset 54 (2 bytes), e_phnum at offset 56 (2 bytes)
        let e_phentsize = u16::from_le_bytes([bytes[54], bytes[55]]) as usize;
        let e_phnum = u16::from_le_bytes([bytes[56], bytes[57]]) as usize;

        // e_shentsize at offset 58 (2 bytes), e_shnum at offset 60 (2 bytes)
        let e_shentsize = u16::from_le_bytes([bytes[58], bytes[59]]) as usize;
        let e_shnum = u16::from_le_bytes([bytes[60], bytes[61]]) as usize;
        let e_shstrndx = u16::from_le_bytes([bytes[62], bytes[63]]) as usize;

        if e_phnum > MAX_PROGRAM_HEADERS {
            return Err(LoaderError::ResourceLimitExceeded {
                resource: "ELF Program Headers".to_string(),
                count: e_phnum,
                limit: MAX_PROGRAM_HEADERS,
            });
        }

        if e_shnum > MAX_SECTIONS {
            return Err(LoaderError::ResourceLimitExceeded {
                resource: "ELF Sections".to_string(),
                count: e_shnum,
                limit: MAX_SECTIONS,
            });
        }

        // 1. Parse Program Header Table (Segment View)
        let mut program_headers = Vec::with_capacity(e_phnum);
        if e_phnum > 0 && e_phoff > 0 {
            if e_phentsize < 56 {
                return Err(LoaderError::MalformedHeader(
                    "ELF program header entry size < 56 bytes".to_string(),
                ));
            }
            let ph_table_len = e_phnum
                .checked_mul(e_phentsize)
                .ok_or_else(|| LoaderError::IntegerOverflow("phnum * phentsize".to_string()))?;
            let ph_table_end = e_phoff
                .checked_add(ph_table_len)
                .ok_or_else(|| LoaderError::IntegerOverflow("phoff + ph_table_len".to_string()))?;
            if ph_table_end > bytes.len() {
                return Err(LoaderError::OutOfBounds {
                    offset: e_phoff,
                    size: ph_table_len,
                    file_len: bytes.len(),
                });
            }

            for i in 0..e_phnum {
                let off = e_phoff + i * e_phentsize;
                let p_type = u32::from_le_bytes([
                    bytes[off],
                    bytes[off + 1],
                    bytes[off + 2],
                    bytes[off + 3],
                ]);
                let p_flags = u32::from_le_bytes([
                    bytes[off + 4],
                    bytes[off + 5],
                    bytes[off + 6],
                    bytes[off + 7],
                ]);
                let p_offset = u64::from_le_bytes([
                    bytes[off + 8],
                    bytes[off + 9],
                    bytes[off + 10],
                    bytes[off + 11],
                    bytes[off + 12],
                    bytes[off + 13],
                    bytes[off + 14],
                    bytes[off + 15],
                ]);
                let p_vaddr = u64::from_le_bytes([
                    bytes[off + 16],
                    bytes[off + 17],
                    bytes[off + 18],
                    bytes[off + 19],
                    bytes[off + 20],
                    bytes[off + 21],
                    bytes[off + 22],
                    bytes[off + 23],
                ]);
                let p_paddr = u64::from_le_bytes([
                    bytes[off + 24],
                    bytes[off + 25],
                    bytes[off + 26],
                    bytes[off + 27],
                    bytes[off + 28],
                    bytes[off + 29],
                    bytes[off + 30],
                    bytes[off + 31],
                ]);
                let p_filesz = u64::from_le_bytes([
                    bytes[off + 32],
                    bytes[off + 33],
                    bytes[off + 34],
                    bytes[off + 35],
                    bytes[off + 36],
                    bytes[off + 37],
                    bytes[off + 38],
                    bytes[off + 39],
                ]);
                let p_memsz = u64::from_le_bytes([
                    bytes[off + 40],
                    bytes[off + 41],
                    bytes[off + 42],
                    bytes[off + 43],
                    bytes[off + 44],
                    bytes[off + 45],
                    bytes[off + 46],
                    bytes[off + 47],
                ]);
                let p_align = u64::from_le_bytes([
                    bytes[off + 48],
                    bytes[off + 49],
                    bytes[off + 50],
                    bytes[off + 51],
                    bytes[off + 52],
                    bytes[off + 53],
                    bytes[off + 54],
                    bytes[off + 55],
                ]);

                // Alignment congruence check for PT_LOAD
                if p_type == PT_LOAD && p_align > 1 && (p_vaddr % p_align) != (p_offset % p_align) {
                    return Err(LoaderError::AlignmentViolation {
                        vaddr: p_vaddr,
                        offset: p_offset,
                        align: p_align,
                    });
                }

                program_headers.push(Elf64ProgramHeader {
                    p_type,
                    p_flags,
                    p_offset,
                    p_vaddr,
                    p_paddr,
                    p_filesz,
                    p_memsz,
                    p_align,
                });
            }
        }

        // Validate entry point containment if PT_LOAD segments exist
        let load_segments: Vec<&Elf64ProgramHeader> =
            program_headers.iter().filter(|p| p.is_load()).collect();
        if !load_segments.is_empty() {
            let in_load = load_segments.iter().any(|seg| {
                entry_point >= seg.p_vaddr && entry_point < seg.p_vaddr.saturating_add(seg.p_memsz)
            });
            if !in_load {
                return Err(LoaderError::EntryPointOutsideSegments { entry_point });
            }
        }

        // 2. Parse Section Header Table
        let mut sections = Vec::with_capacity(e_shnum);
        if e_shnum > 0 && e_shoff > 0 {
            if e_shentsize < 64 {
                return Err(LoaderError::MalformedHeader(
                    "ELF section header entry size < 64 bytes".to_string(),
                ));
            }
            let sh_table_len = e_shnum
                .checked_mul(e_shentsize)
                .ok_or_else(|| LoaderError::IntegerOverflow("shnum * shentsize".to_string()))?;
            let sh_table_end = e_shoff
                .checked_add(sh_table_len)
                .ok_or_else(|| LoaderError::IntegerOverflow("shoff + sh_table_len".to_string()))?;
            if sh_table_end > bytes.len() {
                return Err(LoaderError::OutOfBounds {
                    offset: e_shoff,
                    size: sh_table_len,
                    file_len: bytes.len(),
                });
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
                let off = e_shoff + i * e_shentsize;
                let sh_name = u32::from_le_bytes([
                    bytes[off],
                    bytes[off + 1],
                    bytes[off + 2],
                    bytes[off + 3],
                ]);
                let sh_type = u32::from_le_bytes([
                    bytes[off + 4],
                    bytes[off + 5],
                    bytes[off + 6],
                    bytes[off + 7],
                ]);
                let sh_flags = u64::from_le_bytes([
                    bytes[off + 8],
                    bytes[off + 9],
                    bytes[off + 10],
                    bytes[off + 11],
                    bytes[off + 12],
                    bytes[off + 13],
                    bytes[off + 14],
                    bytes[off + 15],
                ]);
                let sh_addr = u64::from_le_bytes([
                    bytes[off + 16],
                    bytes[off + 17],
                    bytes[off + 18],
                    bytes[off + 19],
                    bytes[off + 20],
                    bytes[off + 21],
                    bytes[off + 22],
                    bytes[off + 23],
                ]);
                let sh_offset = u64::from_le_bytes([
                    bytes[off + 24],
                    bytes[off + 25],
                    bytes[off + 26],
                    bytes[off + 27],
                    bytes[off + 28],
                    bytes[off + 29],
                    bytes[off + 30],
                    bytes[off + 31],
                ]);
                let sh_size = u64::from_le_bytes([
                    bytes[off + 32],
                    bytes[off + 33],
                    bytes[off + 34],
                    bytes[off + 35],
                    bytes[off + 36],
                    bytes[off + 37],
                    bytes[off + 38],
                    bytes[off + 39],
                ]);

                raw_shdrs.push(RawShdr {
                    name_offset: sh_name,
                    sh_type,
                    sh_flags,
                    sh_addr,
                    sh_offset,
                    sh_size,
                });
            }

            let strtab_bytes = if e_shstrndx < raw_shdrs.len() {
                let str_hdr = &raw_shdrs[e_shstrndx];
                let start = str_hdr.sh_offset as usize;
                let size = str_hdr.sh_size as usize;
                if let Some(end) = start.checked_add(size) {
                    if end <= bytes.len() {
                        &bytes[start..end]
                    } else {
                        &[]
                    }
                } else {
                    &[]
                }
            } else {
                &[]
            };

            for (i, raw) in raw_shdrs.into_iter().enumerate() {
                let name = if (raw.name_offset as usize) < strtab_bytes.len() {
                    let name_slice = &strtab_bytes[raw.name_offset as usize..];
                    let null_pos = name_slice
                        .iter()
                        .position(|&b| b == 0)
                        .unwrap_or(name_slice.len());
                    String::from_utf8_lossy(&name_slice[..null_pos]).to_string()
                } else {
                    format!("sec_{}", i)
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
        }

        Ok(Elf64File {
            elf_type,
            entry_point,
            program_headers,
            sections,
        })
    }

    /// Finds a section by name.
    pub fn find_section(&self, name: &str) -> Option<&Elf64Section> {
        self.sections.iter().find(|s| s.name == name)
    }

    /// Maps the ELF binary segments into a runtime `LoadedProcessImage`.
    ///
    /// Applies `load_bias` (crucial for PIE / `ET_DYN` executables), allocates memory
    /// for `PT_LOAD` segments, and guarantees BSS (`p_memsz > p_filesz`) zero-initialization.
    pub fn load_image(
        &self,
        raw: &[u8],
        load_bias: u64,
    ) -> Result<LoadedProcessImage, LoaderError> {
        let load_segments: Vec<&Elf64ProgramHeader> = self
            .program_headers
            .iter()
            .filter(|p| p.is_load())
            .collect();
        let mut segments = Vec::new();

        if !load_segments.is_empty() {
            let mut total_mapped_bytes: usize = 0;
            for seg in load_segments {
                let memsz = seg.p_memsz as usize;
                let filesz = seg.p_filesz as usize;

                total_mapped_bytes = total_mapped_bytes.checked_add(memsz).ok_or_else(|| {
                    LoaderError::IntegerOverflow("total_mapped_bytes".to_string())
                })?;
                if total_mapped_bytes > MAX_IMAGE_SIZE {
                    return Err(LoaderError::ResourceLimitExceeded {
                        resource: "Process Image Mapped Size".to_string(),
                        count: total_mapped_bytes,
                        limit: MAX_IMAGE_SIZE,
                    });
                }

                let mut data = vec![0u8; memsz];
                if filesz > 0 {
                    let file_off = seg.p_offset as usize;
                    let file_end = file_off.checked_add(filesz).ok_or_else(|| {
                        LoaderError::IntegerOverflow("file_off + filesz".to_string())
                    })?;
                    if file_end > raw.len() {
                        return Err(LoaderError::OutOfBounds {
                            offset: file_off,
                            size: filesz,
                            file_len: raw.len(),
                        });
                    }
                    data[..filesz].copy_from_slice(&raw[file_off..file_end]);
                    // Bytes from filesz to memsz remain 0 (BSS zeroing)
                }

                let target_vaddr = seg.p_vaddr.checked_add(load_bias).ok_or_else(|| {
                    LoaderError::IntegerOverflow("p_vaddr + load_bias".to_string())
                })?;

                segments.push(MemorySegment {
                    base_vaddr: target_vaddr,
                    size: memsz,
                    data,
                    is_readable: seg.is_readable(),
                    is_writable: seg.is_writable(),
                    is_executable: seg.is_executable(),
                });
            }

            let biased_entry = self.entry_point.checked_add(load_bias).ok_or_else(|| {
                LoaderError::IntegerOverflow("entry_point + load_bias".to_string())
            })?;

            Ok(LoadedProcessImage {
                base_address: load_bias,
                entry_point: biased_entry,
                segments,
            })
        } else {
            // Fallback to sections if no program headers exist
            let mut total_mapped: usize = 0;
            for sec in self.sections.iter().filter(|s| s.is_alloc()) {
                let size = sec.sh_size as usize;
                total_mapped = total_mapped.saturating_add(size);
                if total_mapped > MAX_IMAGE_SIZE {
                    return Err(LoaderError::ResourceLimitExceeded {
                        resource: "Process Image Mapped Size".to_string(),
                        count: total_mapped,
                        limit: MAX_IMAGE_SIZE,
                    });
                }

                let mut data = vec![0u8; size];
                if sec.sh_type != 8 {
                    // SHT_NOBITS = 8 (BSS)
                    let off = sec.sh_offset as usize;
                    let end = off.checked_add(size).ok_or_else(|| {
                        LoaderError::IntegerOverflow("sec offset + size".to_string())
                    })?;
                    if end <= raw.len() {
                        data.copy_from_slice(&raw[off..end]);
                    }
                }

                let vaddr = sec.sh_addr.checked_add(load_bias).unwrap_or(sec.sh_addr);
                segments.push(MemorySegment {
                    base_vaddr: vaddr,
                    size,
                    data,
                    is_readable: true,
                    is_writable: sec.is_writable(),
                    is_executable: sec.is_executable(),
                });
            }

            Ok(LoadedProcessImage {
                base_address: load_bias,
                entry_point: self
                    .entry_point
                    .checked_add(load_bias)
                    .unwrap_or(self.entry_point),
                segments,
            })
        }
    }

    /// Extracts machine code bytes starting at the entry point.
    pub fn extract_entry_point_bytes<'a>(
        &self,
        raw: &'a [u8],
        max_len: usize,
    ) -> Result<&'a [u8], LoaderError> {
        // 1. Check Program Headers (Segment View)
        for seg in self.program_headers.iter().filter(|p| p.is_load()) {
            if self.entry_point >= seg.p_vaddr
                && self.entry_point < seg.p_vaddr.saturating_add(seg.p_filesz)
            {
                let off_in_seg = (self.entry_point - seg.p_vaddr) as usize;
                let file_start = seg.p_offset as usize + off_in_seg;
                let avail = (seg.p_filesz as usize).saturating_sub(off_in_seg);
                let len = avail.min(max_len);
                if file_start
                    .checked_add(len)
                    .map(|e| e <= raw.len())
                    .unwrap_or(false)
                    && len > 0
                {
                    return Ok(&raw[file_start..file_start + len]);
                }
            }
        }

        // 2. Check Section Table
        for sec in &self.sections {
            if self.entry_point >= sec.sh_addr
                && self.entry_point < sec.sh_addr.saturating_add(sec.sh_size)
            {
                let offset_in_sec = (self.entry_point - sec.sh_addr) as usize;
                let file_start = sec.sh_offset as usize + offset_in_sec;
                let avail = (sec.sh_size as usize).saturating_sub(offset_in_sec);
                let len = avail.min(max_len);
                if file_start
                    .checked_add(len)
                    .map(|e| e <= raw.len())
                    .unwrap_or(false)
                    && len > 0
                {
                    return Ok(&raw[file_start..file_start + len]);
                }
            }
        }

        if let Some(text_sec) = self.find_section(".text") {
            let start = text_sec.sh_offset as usize;
            let len = (text_sec.sh_size as usize).min(max_len);
            if start
                .checked_add(len)
                .map(|e| e <= raw.len())
                .unwrap_or(false)
                && len > 0
            {
                return Ok(&raw[start..start + len]);
            }
        }

        Err(LoaderError::MalformedHeader(
            "Could not locate executable entry point bytes in ELF segments or sections".to_string(),
        ))
    }
}

// -----------------------------------------------------------------------------
// PE32+ (PE64) Runtime Model & Structures
// -----------------------------------------------------------------------------

/// PE Section Characteristics flags.
pub const IMAGE_SCN_CNT_CODE: u32 = 0x00000020;
pub const IMAGE_SCN_CNT_INITIALIZED_DATA: u32 = 0x00000040;
pub const IMAGE_SCN_CNT_UNINITIALIZED_DATA: u32 = 0x00000080;
pub const IMAGE_SCN_MEM_EXECUTE: u32 = 0x20000000;
pub const IMAGE_SCN_MEM_READ: u32 = 0x40000000;
pub const IMAGE_SCN_MEM_WRITE: u32 = 0x80000000;

/// Base relocation type constants.
pub const IMAGE_REL_BASED_ABSOLUTE: u8 = 0;
pub const IMAGE_REL_BASED_DIR64: u8 = 10;

/// Parsed section representation within a PE32+ binary.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PeSection {
    pub name: String,
    pub virtual_size: u32,
    pub virtual_address: u32,
    pub size_of_raw_data: u32,
    pub pointer_to_raw_data: u32,
    pub characteristics: u32,
}

impl PeSection {
    #[inline]
    pub fn is_executable(&self) -> bool {
        (self.characteristics & IMAGE_SCN_MEM_EXECUTE) != 0
            || (self.characteristics & IMAGE_SCN_CNT_CODE) != 0
    }

    #[inline]
    pub fn is_readable(&self) -> bool {
        (self.characteristics & IMAGE_SCN_MEM_READ) != 0
    }

    #[inline]
    pub fn is_writable(&self) -> bool {
        (self.characteristics & IMAGE_SCN_MEM_WRITE) != 0
    }
}

/// PE Data Directory entry (VirtualAddress and Size).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub struct PeDataDirectory {
    pub virtual_address: u32,
    pub size: u32,
}

/// Imported function metadata.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PeImportFunction {
    pub ordinal: Option<u16>,
    pub name: Option<String>,
}

/// Imported module (DLL) and associated function symbols.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PeImport {
    pub dll_name: String,
    pub functions: Vec<PeImportFunction>,
}

/// A parsed base relocation block covering a 4KB memory page.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PeRelocationBlock {
    pub page_rva: u32,
    pub entries: Vec<(u8, u16)>, // (type, offset within page)
}

/// An exported symbol from a PE32+ module.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PeExport {
    pub name: Option<String>,
    pub ordinal: u32,
    pub rva: u32,
    pub forwarder: Option<String>,
}

/// Unwind / exception handling function table entry (.pdata) for x86-64.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PeRuntimeFunction {
    pub begin_address: u32,
    pub end_address: u32,
    pub unwind_info_address: u32,
}

/// PE TLS Directory metadata.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PeTlsDirectory {
    pub start_address_of_raw_data: u64,
    pub end_address_of_raw_data: u64,
    pub address_of_index: u64,
    pub address_of_callbacks: u64,
    pub size_of_zero_fill: u32,
    pub characteristics: u32,
    pub callbacks: Vec<u64>,
}

/// Parsed PE32+ (64-bit) binary structure.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Pe64File {
    pub entry_point_rva: u32,
    pub image_base: u64,
    pub section_alignment: u32,
    pub file_alignment: u32,
    pub sections: Vec<PeSection>,
    pub data_directories: Vec<PeDataDirectory>,
    pub imports: Vec<PeImport>,
    pub delay_imports: Vec<PeImport>,
    pub exports: Vec<PeExport>,
    pub exception_directory: Vec<PeRuntimeFunction>,
    pub relocations: Vec<PeRelocationBlock>,
    pub tls: Option<PeTlsDirectory>,
}

impl Pe64File {
    /// Parses a PE32+ (64-bit) binary from raw bytes with checked arithmetic and resource limits.
    pub fn parse(bytes: &[u8]) -> Result<Self, LoaderError> {
        if bytes.len() < 0x40 {
            return Err(LoaderError::FileTooSmall {
                expected: 0x40,
                actual: bytes.len(),
            });
        }

        if &bytes[0..2] != b"MZ" {
            return Err(LoaderError::InvalidMagic(
                "Expected DOS signature 'MZ'".to_string(),
            ));
        }

        let pe_offset =
            u32::from_le_bytes([bytes[0x3c], bytes[0x3d], bytes[0x3e], bytes[0x3f]]) as usize;
        let pe_sig_end = pe_offset
            .checked_add(24)
            .ok_or_else(|| LoaderError::IntegerOverflow("pe_offset + 24".to_string()))?;
        if pe_sig_end > bytes.len() {
            return Err(LoaderError::OutOfBounds {
                offset: pe_offset,
                size: 24,
                file_len: bytes.len(),
            });
        }

        if &bytes[pe_offset..pe_offset + 4] != b"PE\0\0" {
            return Err(LoaderError::InvalidMagic(
                "Expected PE signature 'PE\\0\\0'".to_string(),
            ));
        }

        let coff_offset = pe_offset + 4;
        let machine = u16::from_le_bytes([bytes[coff_offset], bytes[coff_offset + 1]]);
        if machine != 0x8664 {
            return Err(LoaderError::UnsupportedArchitecture(format!(
                "PE Machine 0x{:04x} is not AMD x86-64 (0x8664)",
                machine
            )));
        }

        let num_sections =
            u16::from_le_bytes([bytes[coff_offset + 2], bytes[coff_offset + 3]]) as usize;
        if num_sections > MAX_SECTIONS {
            return Err(LoaderError::ResourceLimitExceeded {
                resource: "PE Sections".to_string(),
                count: num_sections,
                limit: MAX_SECTIONS,
            });
        }

        let opt_hdr_size =
            u16::from_le_bytes([bytes[coff_offset + 16], bytes[coff_offset + 17]]) as usize;
        let opt_offset = coff_offset + 20;
        let opt_end = opt_offset
            .checked_add(opt_hdr_size)
            .ok_or_else(|| LoaderError::IntegerOverflow("opt_offset + opt_hdr_size".to_string()))?;
        if opt_end > bytes.len() || opt_hdr_size < 112 {
            return Err(LoaderError::MalformedHeader(
                "Optional header truncated or missing (< 112 bytes)".to_string(),
            ));
        }

        let opt_magic = u16::from_le_bytes([bytes[opt_offset], bytes[opt_offset + 1]]);
        if opt_magic != 0x020b {
            return Err(LoaderError::UnsupportedArchitecture(format!(
                "Optional Header magic 0x{:04x} is not PE32+ (0x020b)",
                opt_magic
            )));
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

        let section_alignment = u32::from_le_bytes([
            bytes[opt_offset + 32],
            bytes[opt_offset + 33],
            bytes[opt_offset + 34],
            bytes[opt_offset + 35],
        ]);
        let file_alignment = u32::from_le_bytes([
            bytes[opt_offset + 36],
            bytes[opt_offset + 37],
            bytes[opt_offset + 38],
            bytes[opt_offset + 39],
        ]);

        // Parse Data Directories (offset 112 in Optional Header)
        let num_rva_sizes = if opt_hdr_size >= 112 {
            u32::from_le_bytes([
                bytes[opt_offset + 108],
                bytes[opt_offset + 109],
                bytes[opt_offset + 110],
                bytes[opt_offset + 111],
            ]) as usize
        } else {
            0
        };

        let mut data_directories = Vec::new();
        let dirs_start = opt_offset + 112;
        let max_dirs = num_rva_sizes.min(16);
        if dirs_start
            .checked_add(max_dirs * 8)
            .map(|e| e <= opt_end)
            .unwrap_or(false)
        {
            for i in 0..max_dirs {
                let off = dirs_start + i * 8;
                let va = u32::from_le_bytes([
                    bytes[off],
                    bytes[off + 1],
                    bytes[off + 2],
                    bytes[off + 3],
                ]);
                let sz = u32::from_le_bytes([
                    bytes[off + 4],
                    bytes[off + 5],
                    bytes[off + 6],
                    bytes[off + 7],
                ]);
                data_directories.push(PeDataDirectory {
                    virtual_address: va,
                    size: sz,
                });
            }
        }

        // Parse Section Table
        let sec_table_offset = opt_offset + opt_hdr_size;
        let sec_entry_size = 40;
        let sec_table_len = num_sections
            .checked_mul(sec_entry_size)
            .ok_or_else(|| LoaderError::IntegerOverflow("num_sections * 40".to_string()))?;
        let sec_table_end = sec_table_offset
            .checked_add(sec_table_len)
            .ok_or_else(|| LoaderError::IntegerOverflow("sec_table_offset + len".to_string()))?;
        if sec_table_end > bytes.len() {
            return Err(LoaderError::OutOfBounds {
                offset: sec_table_offset,
                size: sec_table_len,
                file_len: bytes.len(),
            });
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
            let characteristics = u32::from_le_bytes([
                bytes[offset + 36],
                bytes[offset + 37],
                bytes[offset + 38],
                bytes[offset + 39],
            ]);

            sections.push(PeSection {
                name,
                virtual_size,
                virtual_address,
                size_of_raw_data,
                pointer_to_raw_data,
                characteristics,
            });
        }

        // Helper to convert RVA to file offset
        let rva_to_off = |rva: u32| -> Option<usize> {
            for s in &sections {
                let span = s.virtual_size.max(s.size_of_raw_data);
                if rva >= s.virtual_address && rva < s.virtual_address.saturating_add(span) {
                    let off = rva - s.virtual_address;
                    let file_off = s.pointer_to_raw_data as usize + off as usize;
                    if file_off < bytes.len() {
                        return Some(file_off);
                    }
                }
            }
            None
        };

        // Parse Imports (Data Directory 1: IMAGE_DIRECTORY_ENTRY_IMPORT)
        let mut imports = Vec::new();
        if data_directories.len() > 1
            && data_directories[1].size > 0
            && data_directories[1].virtual_address > 0
        {
            let import_rva = data_directories[1].virtual_address;
            if let Some(mut desc_off) = rva_to_off(import_rva) {
                let mut import_count = 0;
                while desc_off + 20 <= bytes.len() && import_count < MAX_IMPORTS {
                    // IMAGE_IMPORT_DESCRIPTOR: OriginalFirstThunk (4), TimeDateStamp (4), ForwarderChain (4), Name (4), FirstThunk (4)
                    let orig_first_thunk = u32::from_le_bytes([
                        bytes[desc_off],
                        bytes[desc_off + 1],
                        bytes[desc_off + 2],
                        bytes[desc_off + 3],
                    ]);
                    let name_rva = u32::from_le_bytes([
                        bytes[desc_off + 12],
                        bytes[desc_off + 13],
                        bytes[desc_off + 14],
                        bytes[desc_off + 15],
                    ]);
                    let first_thunk = u32::from_le_bytes([
                        bytes[desc_off + 16],
                        bytes[desc_off + 17],
                        bytes[desc_off + 18],
                        bytes[desc_off + 19],
                    ]);

                    if orig_first_thunk == 0 && name_rva == 0 && first_thunk == 0 {
                        break; // Null descriptor terminates table
                    }

                    import_count += 1;
                    let dll_name = if let Some(n_off) = rva_to_off(name_rva) {
                        let slice = &bytes[n_off..];
                        let null_pos = slice
                            .iter()
                            .position(|&b| b == 0)
                            .unwrap_or(slice.len().min(64));
                        String::from_utf8_lossy(&slice[..null_pos]).to_string()
                    } else {
                        format!("import_dll_{}", import_count)
                    };

                    let thunk_rva = if orig_first_thunk != 0 {
                        orig_first_thunk
                    } else {
                        first_thunk
                    };
                    let mut functions = Vec::new();
                    if let Some(mut thunk_off) = rva_to_off(thunk_rva) {
                        while thunk_off + 8 <= bytes.len() {
                            let thunk_val = u64::from_le_bytes([
                                bytes[thunk_off],
                                bytes[thunk_off + 1],
                                bytes[thunk_off + 2],
                                bytes[thunk_off + 3],
                                bytes[thunk_off + 4],
                                bytes[thunk_off + 5],
                                bytes[thunk_off + 6],
                                bytes[thunk_off + 7],
                            ]);
                            if thunk_val == 0 {
                                break;
                            }
                            if (thunk_val & (1u64 << 63)) != 0 {
                                // Ordinal import
                                functions.push(PeImportFunction {
                                    ordinal: Some((thunk_val & 0xffff) as u16),
                                    name: None,
                                });
                            } else {
                                // Hint/Name RVA
                                let hint_name_rva = (thunk_val & 0x7fff_ffff) as u32;
                                let name = if let Some(hn_off) = rva_to_off(hint_name_rva) {
                                    if hn_off + 2 < bytes.len() {
                                        let name_slice = &bytes[hn_off + 2..];
                                        let null_p = name_slice
                                            .iter()
                                            .position(|&b| b == 0)
                                            .unwrap_or(name_slice.len().min(128));
                                        Some(
                                            String::from_utf8_lossy(&name_slice[..null_p])
                                                .to_string(),
                                        )
                                    } else {
                                        None
                                    }
                                } else {
                                    None
                                };
                                functions.push(PeImportFunction {
                                    ordinal: None,
                                    name,
                                });
                            }
                            thunk_off += 8;
                        }
                    }

                    imports.push(PeImport {
                        dll_name,
                        functions,
                    });
                    desc_off += 20;
                }
            }
        }

        // Parse Base Relocations (Data Directory 5: IMAGE_DIRECTORY_ENTRY_BASERELOC)
        let mut relocations = Vec::new();
        if data_directories.len() > 5
            && data_directories[5].size > 0
            && data_directories[5].virtual_address > 0
        {
            let reloc_rva = data_directories[5].virtual_address;
            let reloc_size = data_directories[5].size as usize;
            if let Some(start_off) = rva_to_off(reloc_rva) {
                let end_off = start_off
                    .checked_add(reloc_size)
                    .unwrap_or(start_off)
                    .min(bytes.len());
                let mut cur = start_off;
                let mut total_reloc_entries = 0;
                while cur + 8 <= end_off && total_reloc_entries < MAX_RELOCATIONS {
                    let page_rva = u32::from_le_bytes([
                        bytes[cur],
                        bytes[cur + 1],
                        bytes[cur + 2],
                        bytes[cur + 3],
                    ]);
                    let block_size = u32::from_le_bytes([
                        bytes[cur + 4],
                        bytes[cur + 5],
                        bytes[cur + 6],
                        bytes[cur + 7],
                    ]) as usize;
                    if block_size < 8 || cur + block_size > end_off {
                        break;
                    }

                    let num_entries = (block_size - 8) / 2;
                    let mut entries = Vec::with_capacity(num_entries);
                    for j in 0..num_entries {
                        let e_off = cur + 8 + j * 2;
                        let val = u16::from_le_bytes([bytes[e_off], bytes[e_off + 1]]);
                        let r_type = (val >> 12) as u8;
                        let r_offset = val & 0x0fff;
                        entries.push((r_type, r_offset));
                        total_reloc_entries += 1;
                    }
                    relocations.push(PeRelocationBlock { page_rva, entries });
                    cur += block_size;
                }
            }
        }

        // Parse Export Directory (Data Directory 0: IMAGE_DIRECTORY_ENTRY_EXPORT)
        let mut exports = Vec::new();
        if !data_directories.is_empty()
            && data_directories[0].size >= 40
            && data_directories[0].virtual_address > 0
        {
            let exp_dir_rva = data_directories[0].virtual_address;
            let exp_dir_size = data_directories[0].size;
            if let Some(exp_off) = rva_to_off(exp_dir_rva) {
                if exp_off + 40 <= bytes.len() {
                    let ordinal_base = u32::from_le_bytes([
                        bytes[exp_off + 16],
                        bytes[exp_off + 17],
                        bytes[exp_off + 18],
                        bytes[exp_off + 19],
                    ]);
                    let num_functions = u32::from_le_bytes([
                        bytes[exp_off + 20],
                        bytes[exp_off + 21],
                        bytes[exp_off + 22],
                        bytes[exp_off + 23],
                    ]) as usize;
                    let num_names = u32::from_le_bytes([
                        bytes[exp_off + 24],
                        bytes[exp_off + 25],
                        bytes[exp_off + 26],
                        bytes[exp_off + 27],
                    ]) as usize;
                    let addr_functions = u32::from_le_bytes([
                        bytes[exp_off + 28],
                        bytes[exp_off + 29],
                        bytes[exp_off + 30],
                        bytes[exp_off + 31],
                    ]);
                    let addr_names = u32::from_le_bytes([
                        bytes[exp_off + 32],
                        bytes[exp_off + 33],
                        bytes[exp_off + 34],
                        bytes[exp_off + 35],
                    ]);
                    let addr_name_ordinals = u32::from_le_bytes([
                        bytes[exp_off + 36],
                        bytes[exp_off + 37],
                        bytes[exp_off + 38],
                        bytes[exp_off + 39],
                    ]);

                    let capped_funcs = num_functions.min(4096);
                    let capped_names = num_names.min(4096);

                    // Build mapping from function index to name
                    let mut name_map: std::collections::HashMap<u16, String> =
                        std::collections::HashMap::new();
                    if let (Some(names_off), Some(ordinals_off)) =
                        (rva_to_off(addr_names), rva_to_off(addr_name_ordinals))
                    {
                        for i in 0..capped_names {
                            let n_ptr_off = names_off + i * 4;
                            let ord_ptr_off = ordinals_off + i * 2;
                            if n_ptr_off + 4 <= bytes.len() && ord_ptr_off + 2 <= bytes.len() {
                                let name_rva = u32::from_le_bytes([
                                    bytes[n_ptr_off],
                                    bytes[n_ptr_off + 1],
                                    bytes[n_ptr_off + 2],
                                    bytes[n_ptr_off + 3],
                                ]);
                                let func_idx = u16::from_le_bytes([
                                    bytes[ord_ptr_off],
                                    bytes[ord_ptr_off + 1],
                                ]);
                                if let Some(n_off) = rva_to_off(name_rva) {
                                    let mut end = n_off;
                                    while end < bytes.len() && bytes[end] != 0 && end - n_off < 256
                                    {
                                        end += 1;
                                    }
                                    if end < bytes.len() {
                                        let name =
                                            String::from_utf8_lossy(&bytes[n_off..end]).to_string();
                                        name_map.insert(func_idx, name);
                                    }
                                }
                            }
                        }
                    }

                    // Parse function entries
                    if let Some(func_table_off) = rva_to_off(addr_functions) {
                        for i in 0..capped_funcs {
                            let f_off = func_table_off + i * 4;
                            if f_off + 4 <= bytes.len() {
                                let func_rva = u32::from_le_bytes([
                                    bytes[f_off],
                                    bytes[f_off + 1],
                                    bytes[f_off + 2],
                                    bytes[f_off + 3],
                                ]);
                                if func_rva > 0 {
                                    let is_forwarder = func_rva >= exp_dir_rva
                                        && func_rva < exp_dir_rva.saturating_add(exp_dir_size);
                                    let forwarder = if is_forwarder {
                                        rva_to_off(func_rva).map(|fwd_off| {
                                            let mut end = fwd_off;
                                            while end < bytes.len()
                                                && bytes[end] != 0
                                                && end - fwd_off < 256
                                            {
                                                end += 1;
                                            }
                                            String::from_utf8_lossy(&bytes[fwd_off..end])
                                                .to_string()
                                        })
                                    } else {
                                        None
                                    };
                                    let name = name_map.get(&(i as u16)).cloned();
                                    exports.push(PeExport {
                                        name,
                                        ordinal: ordinal_base.wrapping_add(i as u32),
                                        rva: func_rva,
                                        forwarder,
                                    });
                                }
                            }
                        }
                    }
                }
            }
        }

        // Parse Exception Directory (Data Directory 3: IMAGE_DIRECTORY_ENTRY_EXCEPTION, .pdata)
        let mut exception_directory = Vec::new();
        if data_directories.len() > 3
            && data_directories[3].size >= 12
            && data_directories[3].virtual_address > 0
        {
            if let Some(pdata_off) = rva_to_off(data_directories[3].virtual_address) {
                let entry_count = (data_directories[3].size as usize / 12).min(65536);
                for i in 0..entry_count {
                    let cur = pdata_off + i * 12;
                    if cur + 12 <= bytes.len() {
                        let begin_address = u32::from_le_bytes([
                            bytes[cur],
                            bytes[cur + 1],
                            bytes[cur + 2],
                            bytes[cur + 3],
                        ]);
                        let end_address = u32::from_le_bytes([
                            bytes[cur + 4],
                            bytes[cur + 5],
                            bytes[cur + 6],
                            bytes[cur + 7],
                        ]);
                        let unwind_info_address = u32::from_le_bytes([
                            bytes[cur + 8],
                            bytes[cur + 9],
                            bytes[cur + 10],
                            bytes[cur + 11],
                        ]);
                        exception_directory.push(PeRuntimeFunction {
                            begin_address,
                            end_address,
                            unwind_info_address,
                        });
                    }
                }
            }
        }

        // Parse Delay Import Directory (Data Directory 13: IMAGE_DIRECTORY_ENTRY_DELAY_IMPORT)
        let mut delay_imports = Vec::new();
        if data_directories.len() > 13
            && data_directories[13].size >= 32
            && data_directories[13].virtual_address > 0
        {
            if let Some(mut cur_off) = rva_to_off(data_directories[13].virtual_address) {
                let mut desc_count = 0;
                while desc_count < 512 && cur_off + 32 <= bytes.len() {
                    let name_rva = u32::from_le_bytes([
                        bytes[cur_off + 4],
                        bytes[cur_off + 5],
                        bytes[cur_off + 6],
                        bytes[cur_off + 7],
                    ]);
                    let iat_rva = u32::from_le_bytes([
                        bytes[cur_off + 12],
                        bytes[cur_off + 13],
                        bytes[cur_off + 14],
                        bytes[cur_off + 15],
                    ]);
                    let int_rva = u32::from_le_bytes([
                        bytes[cur_off + 16],
                        bytes[cur_off + 17],
                        bytes[cur_off + 18],
                        bytes[cur_off + 19],
                    ]);

                    if name_rva == 0 && int_rva == 0 && iat_rva == 0 {
                        break;
                    }

                    if let Some(name_file_off) = rva_to_off(name_rva) {
                        let mut name_end = name_file_off;
                        while name_end < bytes.len()
                            && bytes[name_end] != 0
                            && name_end - name_file_off < 256
                        {
                            name_end += 1;
                        }
                        let dll_name =
                            String::from_utf8_lossy(&bytes[name_file_off..name_end]).to_string();

                        let lookup_rva = if int_rva > 0 { int_rva } else { iat_rva };
                        let mut functions = Vec::new();
                        if let Some(mut thunk_off) = rva_to_off(lookup_rva) {
                            let mut func_count = 0;
                            while func_count < 4096 && thunk_off + 8 <= bytes.len() {
                                let thunk_val = u64::from_le_bytes([
                                    bytes[thunk_off],
                                    bytes[thunk_off + 1],
                                    bytes[thunk_off + 2],
                                    bytes[thunk_off + 3],
                                    bytes[thunk_off + 4],
                                    bytes[thunk_off + 5],
                                    bytes[thunk_off + 6],
                                    bytes[thunk_off + 7],
                                ]);
                                if thunk_val == 0 {
                                    break;
                                }

                                if (thunk_val & 0x8000_0000_0000_0000) != 0 {
                                    let ordinal = (thunk_val & 0xffff) as u16;
                                    functions.push(PeImportFunction {
                                        ordinal: Some(ordinal),
                                        name: None,
                                    });
                                } else {
                                    let hint_name_rva = (thunk_val & 0xffff_ffff) as u32;
                                    if let Some(hn_off) = rva_to_off(hint_name_rva) {
                                        if hn_off + 2 < bytes.len() {
                                            let name_start = hn_off + 2;
                                            let mut name_end = name_start;
                                            while name_end < bytes.len()
                                                && bytes[name_end] != 0
                                                && name_end - name_start < 256
                                            {
                                                name_end += 1;
                                            }
                                            let fn_name = String::from_utf8_lossy(
                                                &bytes[name_start..name_end],
                                            )
                                            .to_string();
                                            functions.push(PeImportFunction {
                                                ordinal: None,
                                                name: Some(fn_name),
                                            });
                                        }
                                    }
                                }
                                thunk_off += 8;
                                func_count += 1;
                            }
                        }
                        delay_imports.push(PeImport {
                            dll_name,
                            functions,
                        });
                    }

                    cur_off += 32;
                    desc_count += 1;
                }
            }
        }

        // Parse TLS Directory (Data Directory 9: IMAGE_DIRECTORY_ENTRY_TLS)
        let tls = if data_directories.len() > 9
            && data_directories[9].size >= 40
            && data_directories[9].virtual_address > 0
        {
            if let Some(t_off) = rva_to_off(data_directories[9].virtual_address) {
                if t_off + 40 <= bytes.len() {
                    let start_raw = u64::from_le_bytes([
                        bytes[t_off],
                        bytes[t_off + 1],
                        bytes[t_off + 2],
                        bytes[t_off + 3],
                        bytes[t_off + 4],
                        bytes[t_off + 5],
                        bytes[t_off + 6],
                        bytes[t_off + 7],
                    ]);
                    let end_raw = u64::from_le_bytes([
                        bytes[t_off + 8],
                        bytes[t_off + 9],
                        bytes[t_off + 10],
                        bytes[t_off + 11],
                        bytes[t_off + 12],
                        bytes[t_off + 13],
                        bytes[t_off + 14],
                        bytes[t_off + 15],
                    ]);
                    let idx_addr = u64::from_le_bytes([
                        bytes[t_off + 16],
                        bytes[t_off + 17],
                        bytes[t_off + 18],
                        bytes[t_off + 19],
                        bytes[t_off + 20],
                        bytes[t_off + 21],
                        bytes[t_off + 22],
                        bytes[t_off + 23],
                    ]);
                    let cb_addr = u64::from_le_bytes([
                        bytes[t_off + 24],
                        bytes[t_off + 25],
                        bytes[t_off + 26],
                        bytes[t_off + 27],
                        bytes[t_off + 28],
                        bytes[t_off + 29],
                        bytes[t_off + 30],
                        bytes[t_off + 31],
                    ]);
                    let zero_fill = u32::from_le_bytes([
                        bytes[t_off + 32],
                        bytes[t_off + 33],
                        bytes[t_off + 34],
                        bytes[t_off + 35],
                    ]);
                    let chars = u32::from_le_bytes([
                        bytes[t_off + 36],
                        bytes[t_off + 37],
                        bytes[t_off + 38],
                        bytes[t_off + 39],
                    ]);

                    let mut callbacks = Vec::new();
                    if cb_addr > 0 {
                        let cb_rva = (cb_addr.saturating_sub(image_base)) as u32;
                        if let Some(mut cb_off) = rva_to_off(cb_rva) {
                            let mut cb_count = 0;
                            while cb_count < 64 && cb_off + 8 <= bytes.len() {
                                let ptr = u64::from_le_bytes([
                                    bytes[cb_off],
                                    bytes[cb_off + 1],
                                    bytes[cb_off + 2],
                                    bytes[cb_off + 3],
                                    bytes[cb_off + 4],
                                    bytes[cb_off + 5],
                                    bytes[cb_off + 6],
                                    bytes[cb_off + 7],
                                ]);
                                if ptr == 0 {
                                    break;
                                }
                                callbacks.push(ptr);
                                cb_off += 8;
                                cb_count += 1;
                            }
                        }
                    }

                    Some(PeTlsDirectory {
                        start_address_of_raw_data: start_raw,
                        end_address_of_raw_data: end_raw,
                        address_of_index: idx_addr,
                        address_of_callbacks: cb_addr,
                        size_of_zero_fill: zero_fill,
                        characteristics: chars,
                        callbacks,
                    })
                } else {
                    None
                }
            } else {
                None
            }
        } else {
            None
        };

        Ok(Pe64File {
            entry_point_rva,
            image_base,
            section_alignment,
            file_alignment,
            sections,
            data_directories,
            imports,
            delay_imports,
            exports,
            exception_directory,
            relocations,
            tls,
        })
    }

    /// Converts an RVA to a physical file offset.
    pub fn rva_to_file_offset(&self, rva: u32) -> Option<usize> {
        for sec in &self.sections {
            let span = sec.virtual_size.max(sec.size_of_raw_data);
            if rva >= sec.virtual_address && rva < sec.virtual_address.saturating_add(span) {
                let off_in_sec = rva - sec.virtual_address;
                return Some((sec.pointer_to_raw_data + off_in_sec) as usize);
            }
        }
        None
    }

    /// Maps PE sections into memory, zeroes uninitialized data, and applies base relocations if rebased.
    pub fn load_image(
        &self,
        raw: &[u8],
        target_image_base: Option<u64>,
    ) -> Result<LoadedProcessImage, LoaderError> {
        let loaded_base = target_image_base.unwrap_or(self.image_base);
        let mut segments = Vec::new();
        let mut total_mapped: usize = 0;

        for sec in &self.sections {
            let alloc_size = (sec.virtual_size.max(sec.size_of_raw_data)) as usize;
            total_mapped = total_mapped
                .checked_add(alloc_size)
                .ok_or_else(|| LoaderError::IntegerOverflow("PE mapped size".to_string()))?;
            if total_mapped > MAX_IMAGE_SIZE {
                return Err(LoaderError::ResourceLimitExceeded {
                    resource: "PE Image Mapped Size".to_string(),
                    count: total_mapped,
                    limit: MAX_IMAGE_SIZE,
                });
            }

            let mut data = vec![0u8; alloc_size];
            let raw_size = (sec.size_of_raw_data as usize).min(alloc_size);
            if raw_size > 0 && sec.pointer_to_raw_data as usize + raw_size <= raw.len() {
                let start = sec.pointer_to_raw_data as usize;
                data[..raw_size].copy_from_slice(&raw[start..start + raw_size]);
            }

            let sec_vaddr = loaded_base
                .checked_add(sec.virtual_address as u64)
                .ok_or_else(|| LoaderError::IntegerOverflow("sec_vaddr".to_string()))?;

            segments.push(MemorySegment {
                base_vaddr: sec_vaddr,
                size: alloc_size,
                data,
                is_readable: sec.is_readable(),
                is_writable: sec.is_writable(),
                is_executable: sec.is_executable(),
            });
        }

        // Apply 64-bit base relocations if loaded at a different base
        if loaded_base != self.image_base && !self.relocations.is_empty() {
            let delta = loaded_base.wrapping_sub(self.image_base);
            for block in &self.relocations {
                for &(rel_type, offset) in &block.entries {
                    if rel_type == IMAGE_REL_BASED_DIR64 {
                        let target_rva = block.page_rva.saturating_add(offset as u32);
                        // Locate target segment
                        for seg in &mut segments {
                            let rel_vaddr = loaded_base + target_rva as u64;
                            if rel_vaddr >= seg.base_vaddr
                                && rel_vaddr + 8 <= seg.base_vaddr + seg.size as u64
                            {
                                let byte_off = (rel_vaddr - seg.base_vaddr) as usize;
                                let old_ptr = u64::from_le_bytes([
                                    seg.data[byte_off],
                                    seg.data[byte_off + 1],
                                    seg.data[byte_off + 2],
                                    seg.data[byte_off + 3],
                                    seg.data[byte_off + 4],
                                    seg.data[byte_off + 5],
                                    seg.data[byte_off + 6],
                                    seg.data[byte_off + 7],
                                ]);
                                let new_ptr = old_ptr.wrapping_add(delta);
                                seg.data[byte_off..byte_off + 8]
                                    .copy_from_slice(&new_ptr.to_le_bytes());
                                break;
                            }
                        }
                    }
                }
            }
        }

        let entry_point = loaded_base
            .checked_add(self.entry_point_rva as u64)
            .ok_or_else(|| LoaderError::IntegerOverflow("PE entry_point".to_string()))?;

        Ok(LoadedProcessImage {
            base_address: loaded_base,
            entry_point,
            segments,
        })
    }

    /// Extracts entry point machine code bytes from raw PE file bytes.
    pub fn extract_entry_point_bytes<'a>(
        &self,
        raw: &'a [u8],
        max_len: usize,
    ) -> Result<&'a [u8], LoaderError> {
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
            if start
                .checked_add(len)
                .map(|e| e <= raw.len())
                .unwrap_or(false)
                && len > 0
            {
                return Ok(&raw[start..start + len]);
            }
        }

        Err(LoaderError::MalformedHeader(
            "Could not resolve entry point RVA to file offset in PE sections".to_string(),
        ))
    }
}

// -----------------------------------------------------------------------------
// Unified Loaded Process Memory Model
// -----------------------------------------------------------------------------

/// A continuous mapped virtual memory segment.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct MemorySegment {
    pub base_vaddr: u64,
    pub size: usize,
    pub data: Vec<u8>,
    pub is_readable: bool,
    pub is_writable: bool,
    pub is_executable: bool,
}

/// Fully mapped virtual process image ready for symbolic execution and lifter integration.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LoadedProcessImage {
    pub base_address: u64,
    pub entry_point: u64,
    pub segments: Vec<MemorySegment>,
}

impl LoadedProcessImage {
    /// Reads a single byte at virtual address `vaddr`, checking read permissions.
    pub fn read_byte(&self, vaddr: u64) -> Result<u8, LoaderError> {
        for seg in &self.segments {
            if vaddr >= seg.base_vaddr && vaddr < seg.base_vaddr.saturating_add(seg.size as u64) {
                if !seg.is_readable {
                    return Err(LoaderError::MemoryPermissionViolation {
                        vaddr,
                        attempted: "read on non-readable segment",
                    });
                }
                let off = (vaddr - seg.base_vaddr) as usize;
                return Ok(seg.data[off]);
            }
        }
        Err(LoaderError::OutOfBounds {
            offset: vaddr as usize,
            size: 1,
            file_len: 0,
        })
    }

    /// Reads `len` bytes starting at virtual address `vaddr`.
    pub fn read_bytes(&self, vaddr: u64, len: usize) -> Result<Vec<u8>, LoaderError> {
        let mut buf = Vec::with_capacity(len);
        for i in 0..len {
            let addr = vaddr
                .checked_add(i as u64)
                .ok_or_else(|| LoaderError::IntegerOverflow("vaddr + i".to_string()))?;
            buf.push(self.read_byte(addr)?);
        }
        Ok(buf)
    }

    /// Writes a single byte at virtual address `vaddr`, enforcing write permission checks.
    pub fn write_byte(&mut self, vaddr: u64, val: u8) -> Result<(), LoaderError> {
        for seg in &mut self.segments {
            if vaddr >= seg.base_vaddr && vaddr < seg.base_vaddr.saturating_add(seg.size as u64) {
                if !seg.is_writable {
                    return Err(LoaderError::MemoryPermissionViolation {
                        vaddr,
                        attempted: "write on read-only/executable segment",
                    });
                }
                let off = (vaddr - seg.base_vaddr) as usize;
                seg.data[off] = val;
                return Ok(());
            }
        }
        Err(LoaderError::OutOfBounds {
            offset: vaddr as usize,
            size: 1,
            file_len: 0,
        })
    }

    /// Returns true if the address resides in an executable memory segment.
    pub fn is_executable(&self, vaddr: u64) -> bool {
        self.segments.iter().any(|s| {
            s.is_executable
                && vaddr >= s.base_vaddr
                && vaddr < s.base_vaddr.saturating_add(s.size as u64)
        })
    }

    /// Extracts machine code bytes from an executable segment starting at `vaddr`.
    pub fn extract_code_at(&self, vaddr: u64, max_len: usize) -> Result<Vec<u8>, LoaderError> {
        for seg in &self.segments {
            if seg.is_executable
                && vaddr >= seg.base_vaddr
                && vaddr < seg.base_vaddr.saturating_add(seg.size as u64)
            {
                let off = (vaddr - seg.base_vaddr) as usize;
                let avail = seg.size.saturating_sub(off);
                let len = avail.min(max_len);
                return Ok(seg.data[off..off + len].to_vec());
            }
        }
        Err(LoaderError::EntryPointOutsideSegments { entry_point: vaddr })
    }
}

// -----------------------------------------------------------------------------
// High-Level Binary Loader Interface
// -----------------------------------------------------------------------------

/// Unified binary format classifier.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum BinaryFormat {
    Elf64(Elf64File),
    Pe64(Pe64File),
    RawMachineCode,
}

/// High-level loader detecting format and mapping binaries.
pub struct BinaryLoader;

impl BinaryLoader {
    /// Detects format (ELF64, PE64, or raw machine code) and extracts the entry point code buffer.
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

    /// Fully loads a binary into an executable virtual memory image (`LoadedProcessImage`).
    pub fn load_process_image(
        bytes: &[u8],
        load_bias_or_target_base: Option<u64>,
    ) -> Result<(BinaryFormat, LoadedProcessImage), LoaderError> {
        if bytes.len() >= 4 && &bytes[0..4] == b"\x7fELF" {
            let elf = Elf64File::parse(bytes)?;
            let bias = load_bias_or_target_base.unwrap_or(0);
            let image = elf.load_image(bytes, bias)?;
            return Ok((BinaryFormat::Elf64(elf), image));
        }

        if bytes.len() >= 2 && &bytes[0..2] == b"MZ" {
            let pe = Pe64File::parse(bytes)?;
            let image = pe.load_image(bytes, load_bias_or_target_base)?;
            return Ok((BinaryFormat::Pe64(pe), image));
        }

        // Raw machine code fallback
        let base = load_bias_or_target_base.unwrap_or(0x1000);
        let segment = MemorySegment {
            base_vaddr: base,
            size: bytes.len(),
            data: bytes.to_vec(),
            is_readable: true,
            is_writable: true,
            is_executable: true,
        };
        Ok((
            BinaryFormat::RawMachineCode,
            LoadedProcessImage {
                base_address: base,
                entry_point: base,
                segments: vec![segment],
            },
        ))
    }
}
