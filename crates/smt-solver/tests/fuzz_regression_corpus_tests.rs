//! Permanent regression test corpus of malformed, semi-valid, and logically conflicting
//! ELF64 and PE32+ binaries, verifying the zero-panic guarantee and strict structured errors.

use smt_solver::binary_loader::{Elf64File, LoaderError, Pe64File};

#[test]
fn test_fuzz_regression_truncated_binaries_zero_panic() {
    // Binary shorter than minimal header
    for len in 0..64 {
        let buf = vec![0x7fu8; len];
        let res_elf = Elf64File::parse(&buf);
        assert!(matches!(
            res_elf,
            Err(LoaderError::FileTooSmall { .. }) | Err(LoaderError::InvalidMagic(_))
        ));

        let res_pe = Pe64File::parse(&buf);
        assert!(matches!(
            res_pe,
            Err(LoaderError::FileTooSmall { .. }) | Err(LoaderError::InvalidMagic(_))
        ));
    }
}

#[test]
fn test_fuzz_regression_elf_conflicting_segments_and_alignment_violations() {
    let mut elf = vec![0u8; 256];
    elf[0..4].copy_from_slice(b"\x7fELF");
    elf[4] = 2; // 64-bit
    elf[5] = 1; // Little-endian
    elf[16..18].copy_from_slice(&2u16.to_le_bytes()); // ET_EXEC
    elf[18..20].copy_from_slice(&0x3eu16.to_le_bytes()); // EM_X86_64
    elf[24..32].copy_from_slice(&0x401000u64.to_le_bytes()); // Entry = 0x401000
    elf[32..40].copy_from_slice(&64u64.to_le_bytes()); // e_phoff = 64
    elf[54..56].copy_from_slice(&56u16.to_le_bytes()); // e_phentsize = 56
    elf[56..58].copy_from_slice(&1u16.to_le_bytes()); // e_phnum = 1

    // Program header 0 at offset 64: PT_LOAD
    let ph = 64;
    elf[ph..ph + 4].copy_from_slice(&1u32.to_le_bytes()); // PT_LOAD
    elf[ph + 4..ph + 8].copy_from_slice(&5u32.to_le_bytes()); // PF_R | PF_X
    elf[ph + 8..ph + 16].copy_from_slice(&0x100u64.to_le_bytes()); // p_offset = 0x100
    elf[ph + 16..ph + 24].copy_from_slice(&0x401000u64.to_le_bytes()); // p_vaddr = 0x401000
    elf[ph + 32..ph + 40].copy_from_slice(&0x80u64.to_le_bytes()); // p_filesz = 0x80
    elf[ph + 40..ph + 48].copy_from_slice(&0x80u64.to_le_bytes()); // p_memsz = 0x80
                                                                   // Incongruent alignment: p_align = 0x1000, but (0x401000 % 0x1000 = 0) != (0x100 % 0x1000 = 0x100)
    elf[ph + 48..ph + 56].copy_from_slice(&0x1000u64.to_le_bytes());

    let res = Elf64File::parse(&elf);
    assert!(
        matches!(res, Err(LoaderError::AlignmentViolation { .. })),
        "Expected alignment congruence violation error, got {:?}",
        res
    );
}

#[test]
fn test_fuzz_regression_elf_entry_point_outside_segments() {
    let mut elf = vec![0u8; 512];
    elf[0..4].copy_from_slice(b"\x7fELF");
    elf[4] = 2; // 64-bit
    elf[5] = 1; // Little-endian
    elf[16..18].copy_from_slice(&2u16.to_le_bytes()); // ET_EXEC
    elf[18..20].copy_from_slice(&0x3eu16.to_le_bytes()); // EM_X86_64
    elf[24..32].copy_from_slice(&0x900000u64.to_le_bytes()); // Entry 0x900000 far outside segment
    elf[32..40].copy_from_slice(&64u64.to_le_bytes()); // e_phoff = 64
    elf[54..56].copy_from_slice(&56u16.to_le_bytes()); // e_phentsize = 56
    elf[56..58].copy_from_slice(&1u16.to_le_bytes()); // e_phnum = 1

    let ph = 64;
    elf[ph..ph + 4].copy_from_slice(&1u32.to_le_bytes()); // PT_LOAD
    elf[ph + 4..ph + 8].copy_from_slice(&5u32.to_le_bytes()); // PF_R | PF_X
    elf[ph + 8..ph + 16].copy_from_slice(&0x80u64.to_le_bytes()); // p_offset = 0x80
    elf[ph + 16..ph + 24].copy_from_slice(&0x401080u64.to_le_bytes()); // p_vaddr = 0x401080
    elf[ph + 32..ph + 40].copy_from_slice(&0x80u64.to_le_bytes()); // p_filesz = 0x80
    elf[ph + 40..ph + 48].copy_from_slice(&0x80u64.to_le_bytes()); // p_memsz = 0x80
    elf[ph + 48..ph + 56].copy_from_slice(&0x100u64.to_le_bytes()); // p_align = 0x100

    let res = Elf64File::parse(&elf);
    assert!(
        matches!(res, Err(LoaderError::EntryPointOutsideSegments { entry_point }) if entry_point == 0x900000),
        "Expected EntryPointOutsideSegments, got {:?}",
        res
    );
}

#[test]
fn test_fuzz_regression_pe_corrupted_offsets_and_infinite_bounds() {
    let mut pe = vec![0u8; 1024];
    pe[0] = b'M';
    pe[1] = b'Z';
    // e_lfanew points way beyond file size
    pe[0x3c..0x40].copy_from_slice(&0x8000_0000u32.to_le_bytes());
    let res = Pe64File::parse(&pe);
    assert!(matches!(
        res,
        Err(LoaderError::OutOfBounds { .. }) | Err(LoaderError::IntegerOverflow(_))
    ));

    // Valid e_lfanew but corrupted machine architecture
    pe[0x3c..0x40].copy_from_slice(&0x80u32.to_le_bytes());
    pe[0x80..0x84].copy_from_slice(b"PE\0\0");
    pe[0x84..0x86].copy_from_slice(&0x014cu16.to_le_bytes()); // i386 (32-bit), not 0x8664
    let res_arch = Pe64File::parse(&pe);
    assert!(matches!(
        res_arch,
        Err(LoaderError::UnsupportedArchitecture(_))
    ));
}

#[test]
fn test_fuzz_regression_pe_resource_limits_rejection() {
    let mut pe = vec![0u8; 2048];
    pe[0] = b'M';
    pe[1] = b'Z';
    pe[0x3c..0x40].copy_from_slice(&0x80u32.to_le_bytes());
    pe[0x80..0x84].copy_from_slice(b"PE\0\0");
    pe[0x84..0x86].copy_from_slice(&0x8664u16.to_le_bytes());
    // 600 sections (exceeds MAX_SECTIONS = 512)
    pe[0x86..0x88].copy_from_slice(&600u16.to_le_bytes());

    let res = Pe64File::parse(&pe);
    assert!(
        matches!(res, Err(LoaderError::ResourceLimitExceeded { ref resource, count, limit }) if resource == "PE Sections" && count == 600 && limit == 512)
    );
}
