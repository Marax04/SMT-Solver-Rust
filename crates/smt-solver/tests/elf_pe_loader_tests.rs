//! Integration tests for ELF64 and PE64 header parsing and automated basic block extraction.

use smt_solver::binary_loader::{BinaryFormat, BinaryLoader, Elf64File, Pe64File};
use smt_solver::lifter::{BranchResolution, Lifter};

#[test]
fn test_elf64_synthetic_header_and_basic_block_extraction() {
    // Construct minimal valid ELF64 header with .text and .shstrtab sections
    let mut elf_bytes = vec![0u8; 512];

    // e_ident
    elf_bytes[0..4].copy_from_slice(b"\x7fELF");
    elf_bytes[4] = 2; // 64-bit
    elf_bytes[5] = 1; // little-endian
    elf_bytes[6] = 1; // version

    // e_type = ET_EXEC (2)
    elf_bytes[16..18].copy_from_slice(&2u16.to_le_bytes());
    // e_machine = EM_X86_64 (0x3E)
    elf_bytes[18..20].copy_from_slice(&0x3eu16.to_le_bytes());
    // e_version = 1
    elf_bytes[20..24].copy_from_slice(&1u32.to_le_bytes());

    // e_entry = 0x401000 (virtual address)
    elf_bytes[24..32].copy_from_slice(&0x401000u64.to_le_bytes());
    // e_phoff = 0
    // e_shoff = 0x100 (section headers at byte 256)
    elf_bytes[40..48].copy_from_slice(&0x100u64.to_le_bytes());
    // e_ehsize = 64
    elf_bytes[52..54].copy_from_slice(&64u16.to_le_bytes());
    // e_shentsize = 64
    elf_bytes[58..60].copy_from_slice(&64u16.to_le_bytes());
    // e_shnum = 3 (null, .text, .shstrtab)
    elf_bytes[60..62].copy_from_slice(&3u16.to_le_bytes());
    // e_shstrndx = 2
    elf_bytes[62..64].copy_from_slice(&2u16.to_le_bytes());

    // Payload .text machine code at file offset 0x80 (128):
    // xor eax, eax (31 c0)
    // test eax, eax (85 c0)
    // jz +5 (74 05)
    let text_code: [u8; 6] = [0x31, 0xc0, 0x85, 0xc0, 0x74, 0x05];
    elf_bytes[0x80..0x80 + 6].copy_from_slice(&text_code);

    // .shstrtab contents at file offset 0xc0 (192): "\0.text\0.shstrtab\0"
    let shstrtab_data = b"\0.text\0.shstrtab\0";
    elf_bytes[0xc0..0xc0 + shstrtab_data.len()].copy_from_slice(shstrtab_data);

    // Section 0: Null section at 0x100 (64 zeroes)
    // Section 1: .text at 0x140 (offset 320)
    let sec1_off = 0x100 + 64;
    elf_bytes[sec1_off..sec1_off + 4].copy_from_slice(&1u32.to_le_bytes()); // sh_name = 1 (".text")
    elf_bytes[sec1_off + 4..sec1_off + 8].copy_from_slice(&1u32.to_le_bytes()); // SHT_PROGBITS = 1
    elf_bytes[sec1_off + 8..sec1_off + 16].copy_from_slice(&6u64.to_le_bytes()); // SHF_ALLOC | SHF_EXECINSTR
    elf_bytes[sec1_off + 16..sec1_off + 24].copy_from_slice(&0x401000u64.to_le_bytes()); // sh_addr
    elf_bytes[sec1_off + 24..sec1_off + 32].copy_from_slice(&0x80u64.to_le_bytes()); // sh_offset
    elf_bytes[sec1_off + 32..sec1_off + 40].copy_from_slice(&6u64.to_le_bytes()); // sh_size

    // Section 2: .shstrtab at 0x180 (offset 384)
    let sec2_off = 0x100 + 128;
    elf_bytes[sec2_off..sec2_off + 4].copy_from_slice(&7u32.to_le_bytes()); // sh_name = 7 (".shstrtab")
    elf_bytes[sec2_off + 4..sec2_off + 8].copy_from_slice(&3u32.to_le_bytes()); // SHT_STRTAB = 3
    elf_bytes[sec2_off + 24..sec2_off + 32].copy_from_slice(&0xc0u64.to_le_bytes()); // sh_offset
    elf_bytes[sec2_off + 32..sec2_off + 40]
        .copy_from_slice(&(shstrtab_data.len() as u64).to_le_bytes());

    // 1. Test Elf64Parser directly
    let parsed = Elf64File::parse(&elf_bytes).expect("Valid ELF64 parse");
    assert_eq!(parsed.entry_point, 0x401000);
    assert_eq!(parsed.sections.len(), 3);
    assert!(parsed.find_section(".text").is_some());

    // 2. Extract code
    let code = parsed
        .extract_entry_point_bytes(&elf_bytes, 64)
        .expect("Extract .text code");
    assert_eq!(code, &text_code);

    // 3. Test high-level BinaryLoader
    let (fmt, extracted_code, ep) = BinaryLoader::detect_and_extract(&elf_bytes);
    assert!(matches!(fmt, BinaryFormat::Elf64(_)));
    assert_eq!(ep, 0x401000);
    assert_eq!(extracted_code, &text_code);

    // 4. Feed extracted code into Lifter and verify deterministic SMT branch resolution
    let mut lifter = Lifter::new();
    let instrs = lifter
        .decode_and_execute_bytes(extracted_code, ep)
        .expect("Lift instructions");
    assert_eq!(instrs.len(), 3);
    let term = instrs.last().unwrap();
    let resolution = lifter.resolve_branch(term, &[]);
    // xor eax, eax; test eax, eax -> ZF=1 -> jz branches deterministically to 0x401000 + 6 + 5 = 0x40100b
    assert_eq!(resolution, BranchResolution::Deterministic(0x40100b));
}

#[test]
fn test_pe64_synthetic_header_and_basic_block_extraction() {
    // Construct minimal valid PE32+ header with .text section
    let mut pe_bytes = vec![0u8; 1024];

    // DOS header: MZ magic and e_lfanew
    pe_bytes[0..2].copy_from_slice(b"MZ");
    let pe_header_offset: u32 = 0x80;
    pe_bytes[0x3c..0x40].copy_from_slice(&pe_header_offset.to_le_bytes());

    // PE signature: PE\0\0
    let pe_start = pe_header_offset as usize;
    pe_bytes[pe_start..pe_start + 4].copy_from_slice(b"PE\0\0");

    // COFF Header
    let coff = pe_start + 4;
    pe_bytes[coff..coff + 2].copy_from_slice(&0x8664u16.to_le_bytes()); // Machine AMD64
    pe_bytes[coff + 2..coff + 4].copy_from_slice(&1u16.to_le_bytes()); // 1 Section
    let opt_hdr_size: u16 = 240;
    pe_bytes[coff + 16..coff + 18].copy_from_slice(&opt_hdr_size.to_le_bytes());

    // Optional Header 64
    let opt = coff + 20;
    pe_bytes[opt..opt + 2].copy_from_slice(&0x020bu16.to_le_bytes()); // PE32+ magic
    pe_bytes[opt + 16..opt + 20].copy_from_slice(&0x1000u32.to_le_bytes()); // AddressOfEntryPoint RVA = 0x1000
    pe_bytes[opt + 24..opt + 32].copy_from_slice(&0x140000000u64.to_le_bytes()); // ImageBase

    // Section table at opt + opt_hdr_size
    let sec_table = opt + opt_hdr_size as usize;
    pe_bytes[sec_table..sec_table + 5].copy_from_slice(b".text");
    pe_bytes[sec_table + 8..sec_table + 12].copy_from_slice(&0x200u32.to_le_bytes()); // VirtualSize
    pe_bytes[sec_table + 12..sec_table + 16].copy_from_slice(&0x1000u32.to_le_bytes()); // VirtualAddress RVA
    pe_bytes[sec_table + 16..sec_table + 20].copy_from_slice(&0x200u32.to_le_bytes()); // SizeOfRawData
    pe_bytes[sec_table + 20..sec_table + 24].copy_from_slice(&0x200u32.to_le_bytes()); // PointerToRawData file offset (512)

    // Payload .text machine code at file offset 512 (0x200):
    // mov eax, 42 (b8 2a 00 00 00)
    // cmp eax, 42 (83 f8 2a)
    // jz +10 (74 0a)
    let payload: [u8; 10] = [0xb8, 0x2a, 0x00, 0x00, 0x00, 0x83, 0xf8, 0x2a, 0x74, 0x0a];
    pe_bytes[0x200..0x200 + 10].copy_from_slice(&payload);

    // 1. Parse PE64
    let pe = Pe64File::parse(&pe_bytes).expect("Valid PE64 parse");
    assert_eq!(pe.entry_point_rva, 0x1000);
    assert_eq!(pe.image_base, 0x140000000);
    assert_eq!(pe.sections.len(), 1);

    // 2. Extract code
    let code = pe
        .extract_entry_point_bytes(&pe_bytes, 64)
        .expect("Extract PE entry code");
    assert_eq!(&code[..payload.len()], &payload);

    // 3. Test BinaryLoader
    let (fmt, extracted_code, ep) = BinaryLoader::detect_and_extract(&pe_bytes);
    assert!(matches!(fmt, BinaryFormat::Pe64(_)));
    assert_eq!(ep, 0x140001000);
    assert_eq!(&extracted_code[..payload.len()], &payload);

    // 4. Symbolic execution and SMT resolution
    let mut lifter = Lifter::new();
    let instrs = lifter
        .decode_and_execute_bytes(extracted_code, ep)
        .expect("Lift PE code");
    assert_eq!(instrs.len(), 3);
    let term = instrs.last().unwrap();
    let resolution = lifter.resolve_branch(term, &[]);
    // mov eax, 42; cmp eax, 42 -> ZF=1 -> jz target = 0x140001000 + 10 + 10 = 0x140001014
    assert_eq!(resolution, BranchResolution::Deterministic(0x140001014));
}
