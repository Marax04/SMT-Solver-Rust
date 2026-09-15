//! Adversarial fuzzing and security boundary tests for ELF64 and PE32+ loaders.
//!
//! Validates that the loader never panics on corrupted, truncated, malformed,
//! or adversarial binary inputs, strictly enforcing checked arithmetic and resource limits.

use smt_solver::binary_loader::{
    BinaryFormat, BinaryLoader, Elf64File, LoaderError, Pe64File, MAX_PROGRAM_HEADERS, MAX_SECTIONS,
};

#[test]
fn test_elf_truncated_files_return_error_no_panic() {
    for len in 0..64 {
        let truncated = [0x7f, b'E', b'L', b'F', 2, 1, 1];
        let slice = &truncated[..len.min(truncated.len())];
        let res = Elf64File::parse(slice);
        assert!(res.is_err());
        assert!(matches!(res.unwrap_err(), LoaderError::FileTooSmall { .. }));
    }
}

#[test]
fn test_pe_truncated_files_return_error_no_panic() {
    for len in 0..0x40 {
        let truncated = [b'M', b'Z', 0, 0];
        let slice = &truncated[..len.min(truncated.len())];
        let res = Pe64File::parse(slice);
        assert!(res.is_err());
        assert!(matches!(res.unwrap_err(), LoaderError::FileTooSmall { .. }));
    }
}

#[test]
fn test_elf_invalid_magics_and_unsupported_arch() {
    let mut bad_magic = vec![0u8; 128];
    bad_magic[0..4].copy_from_slice(b"\x7fXYZ");
    let res = Elf64File::parse(&bad_magic);
    assert!(matches!(res, Err(LoaderError::InvalidMagic(_))));

    // Valid ELF magic, but 32-bit class (EI_CLASS = 1)
    bad_magic[0..4].copy_from_slice(b"\x7fELF");
    bad_magic[4] = 1;
    let res = Elf64File::parse(&bad_magic);
    assert!(matches!(res, Err(LoaderError::UnsupportedArchitecture(_))));

    // 64-bit, but big-endian (EI_DATA = 2)
    bad_magic[4] = 2;
    bad_magic[5] = 2;
    let res = Elf64File::parse(&bad_magic);
    assert!(matches!(res, Err(LoaderError::UnsupportedArchitecture(_))));

    // Little-endian, but ARM machine (0x28) instead of x86-64 (0x3e)
    bad_magic[5] = 1;
    bad_magic[18..20].copy_from_slice(&0x28u16.to_le_bytes());
    let res = Elf64File::parse(&bad_magic);
    assert!(matches!(res, Err(LoaderError::UnsupportedArchitecture(_))));
}

#[test]
fn test_elf_resource_limit_exceeded_phnum_and_shnum() {
    let mut buf = vec![0u8; 256];
    buf[0..4].copy_from_slice(b"\x7fELF");
    buf[4] = 2; // 64-bit
    buf[5] = 1; // little-endian
    buf[18..20].copy_from_slice(&0x3eu16.to_le_bytes()); // x86-64

    // Excess phnum > MAX_PROGRAM_HEADERS (256)
    buf[54..56].copy_from_slice(&56u16.to_le_bytes()); // phentsize
    buf[56..58].copy_from_slice(&((MAX_PROGRAM_HEADERS + 1) as u16).to_le_bytes());
    let res = Elf64File::parse(&buf);
    assert!(matches!(
        res,
        Err(LoaderError::ResourceLimitExceeded { .. })
    ));

    // Reset phnum, excess shnum > MAX_SECTIONS (512)
    buf[56..58].copy_from_slice(&0u16.to_le_bytes());
    buf[58..60].copy_from_slice(&64u16.to_le_bytes());
    buf[60..62].copy_from_slice(&((MAX_SECTIONS + 1) as u16).to_le_bytes());
    let res = Elf64File::parse(&buf);
    assert!(matches!(
        res,
        Err(LoaderError::ResourceLimitExceeded { .. })
    ));
}

#[test]
fn test_elf_alignment_congruence_violation() {
    let mut buf = vec![0u8; 512];
    buf[0..4].copy_from_slice(b"\x7fELF");
    buf[4] = 2;
    buf[5] = 1;
    buf[18..20].copy_from_slice(&0x3eu16.to_le_bytes());
    buf[24..32].copy_from_slice(&0x401000u64.to_le_bytes()); // entry
    buf[32..40].copy_from_slice(&64u64.to_le_bytes()); // phoff = 64
    buf[54..56].copy_from_slice(&56u16.to_le_bytes()); // phentsize = 56
    buf[56..58].copy_from_slice(&1u16.to_le_bytes()); // phnum = 1

    // Program header at offset 64:
    // p_type = PT_LOAD (1)
    buf[64..68].copy_from_slice(&1u32.to_le_bytes());
    buf[68..72].copy_from_slice(&5u32.to_le_bytes()); // PF_R | PF_X
                                                      // p_offset = 0x80 (128)
    buf[72..80].copy_from_slice(&0x80u64.to_le_bytes());
    // p_vaddr = 0x401000
    buf[80..88].copy_from_slice(&0x401000u64.to_le_bytes());
    buf[96..104].copy_from_slice(&0x100u64.to_le_bytes()); // filesz
    buf[104..112].copy_from_slice(&0x100u64.to_le_bytes()); // memsz
                                                            // p_align = 0x1000 (4096)
                                                            // Congruence check: vaddr % align == 0x401000 % 0x1000 = 0.
                                                            // offset % align == 0x80 % 0x1000 = 0x80 != 0 -> AlignmentViolation!
    buf[112..120].copy_from_slice(&0x1000u64.to_le_bytes());

    let res = Elf64File::parse(&buf);
    assert!(matches!(res, Err(LoaderError::AlignmentViolation { .. })));
}

#[test]
fn test_pe_invalid_signatures_and_bounds() {
    let mut buf = vec![0u8; 512];
    buf[0..2].copy_from_slice(b"MZ");
    // e_lfanew points beyond file length
    buf[0x3c..0x40].copy_from_slice(&0x10000u32.to_le_bytes());
    let res = Pe64File::parse(&buf);
    assert!(matches!(res, Err(LoaderError::OutOfBounds { .. })));

    // e_lfanew valid offset 0x80, but invalid PE signature
    buf[0x3c..0x40].copy_from_slice(&0x80u32.to_le_bytes());
    buf[0x80..0x84].copy_from_slice(b"NE\0\0");
    let res = Pe64File::parse(&buf);
    assert!(matches!(res, Err(LoaderError::InvalidMagic(_))));

    // Valid PE signature, but 32-bit x86 machine (0x014c)
    buf[0x80..0x84].copy_from_slice(b"PE\0\0");
    buf[0x84..0x86].copy_from_slice(&0x014cu16.to_le_bytes());
    let res = Pe64File::parse(&buf);
    assert!(matches!(res, Err(LoaderError::UnsupportedArchitecture(_))));
}

#[test]
fn test_mutational_stream_fuzzing_zero_panics() {
    // Deterministic pseudo-random mutational fuzzing over 2,000 corrupt/adversarial payloads
    let mut state = 0x1337_c0de_u64;
    let mut next_u8 = || -> u8 {
        state = state
            .wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        (state >> 56) as u8
    };

    for iter in 0..2000 {
        let len = (next_u8() as usize) * 4 + 16;
        let mut buffer = vec![0u8; len];
        for b in &mut buffer {
            *b = next_u8();
        }

        if iter % 3 == 0 && buffer.len() >= 4 {
            buffer[0..4].copy_from_slice(b"\x7fELF");
        } else if iter % 3 == 1 && buffer.len() >= 2 {
            buffer[0..2].copy_from_slice(b"MZ");
        }

        // Must never panic
        let _ = Elf64File::parse(&buffer);
        let _ = Pe64File::parse(&buffer);
        let (fmt, code, _ep) = BinaryLoader::detect_and_extract(&buffer);
        assert!(!code.is_empty() || buffer.is_empty());
        let _ = BinaryLoader::load_process_image(&buffer, None);
        let _ = matches!(
            fmt,
            BinaryFormat::Elf64(_) | BinaryFormat::Pe64(_) | BinaryFormat::RawMachineCode
        );
    }
}
