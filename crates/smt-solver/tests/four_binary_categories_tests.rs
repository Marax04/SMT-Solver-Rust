//! Integration validation across the four fundamental binary execution categories:
//! 1. Static Non-PIE ELF64 (fixed virtual addressing, PT_LOAD segments, BSS zeroing)
//! 2. PIE ELF64 with Load Bias (ET_DYN, position-independent mapping, rebased entry)
//! 3. PE32+ with Import Directory Table and IAT resolution
//! 4. PE32+ Relocatable loaded at Rebased ImageBase (base relocation patching)

use smt_solver::binary_loader::{
    Elf64File, Pe64File, IMAGE_REL_BASED_DIR64, IMAGE_SCN_MEM_EXECUTE, IMAGE_SCN_MEM_READ,
    IMAGE_SCN_MEM_WRITE, PF_R, PF_W, PF_X, PT_LOAD,
};
use smt_solver::lifter::{BranchResolution, Lifter};

// -----------------------------------------------------------------------------
// Category 1: Static Non-PIE ELF64
// -----------------------------------------------------------------------------
#[test]
fn test_category1_static_non_pie_elf64_with_segments_and_bss() {
    let mut elf_bytes = vec![0u8; 1024];

    // e_ident
    elf_bytes[0..4].copy_from_slice(b"\x7fELF");
    elf_bytes[4] = 2; // 64-bit
    elf_bytes[5] = 1; // little-endian
    elf_bytes[6] = 1; // version

    // e_type = ET_EXEC (2)
    elf_bytes[16..18].copy_from_slice(&2u16.to_le_bytes());
    // e_machine = EM_X86_64 (0x3E)
    elf_bytes[18..20].copy_from_slice(&0x3eu16.to_le_bytes());
    // e_entry = 0x401000
    elf_bytes[24..32].copy_from_slice(&0x401000u64.to_le_bytes());
    // e_phoff = 64 (immediately follows header)
    elf_bytes[32..40].copy_from_slice(&64u64.to_le_bytes());
    // e_ehsize = 64, e_phentsize = 56, e_phnum = 2
    elf_bytes[52..54].copy_from_slice(&64u16.to_le_bytes());
    elf_bytes[54..56].copy_from_slice(&56u16.to_le_bytes());
    elf_bytes[56..58].copy_from_slice(&2u16.to_le_bytes());

    // Machine code payload at file offset 0x100 (256):
    // xor eax, eax (31 c0)
    // test eax, eax (85 c0)
    // jz +7 (74 07)
    let code = [0x31, 0xc0, 0x85, 0xc0, 0x74, 0x07];
    elf_bytes[0x100..0x100 + code.len()].copy_from_slice(&code);

    // Segment 0: Code segment (PT_LOAD, PF_R | PF_X)
    let ph0 = 64;
    elf_bytes[ph0..ph0 + 4].copy_from_slice(&PT_LOAD.to_le_bytes());
    elf_bytes[ph0 + 4..ph0 + 8].copy_from_slice(&(PF_R | PF_X).to_le_bytes());
    elf_bytes[ph0 + 8..ph0 + 16].copy_from_slice(&0x100u64.to_le_bytes()); // p_offset = 256
    elf_bytes[ph0 + 16..ph0 + 24].copy_from_slice(&0x401000u64.to_le_bytes()); // p_vaddr
    elf_bytes[ph0 + 24..ph0 + 32].copy_from_slice(&0x401000u64.to_le_bytes()); // p_paddr
    elf_bytes[ph0 + 32..ph0 + 40].copy_from_slice(&0x100u64.to_le_bytes()); // p_filesz = 256
    elf_bytes[ph0 + 40..ph0 + 48].copy_from_slice(&0x100u64.to_le_bytes()); // p_memsz = 256
    elf_bytes[ph0 + 48..ph0 + 56].copy_from_slice(&0x100u64.to_le_bytes()); // p_align = 256 (0x401000 % 0x100 == 0x100 % 0x100 == 0)

    // Segment 1: Data + BSS segment (PT_LOAD, PF_R | PF_W)
    let ph1 = 64 + 56;
    elf_bytes[ph1..ph1 + 4].copy_from_slice(&PT_LOAD.to_le_bytes());
    elf_bytes[ph1 + 4..ph1 + 8].copy_from_slice(&(PF_R | PF_W).to_le_bytes());
    elf_bytes[ph1 + 8..ph1 + 16].copy_from_slice(&0x200u64.to_le_bytes()); // p_offset = 512
    elf_bytes[ph1 + 16..ph1 + 24].copy_from_slice(&0x402000u64.to_le_bytes()); // p_vaddr
    elf_bytes[ph1 + 24..ph1 + 32].copy_from_slice(&0x402000u64.to_le_bytes());
    elf_bytes[ph1 + 32..ph1 + 40].copy_from_slice(&0x40u64.to_le_bytes()); // p_filesz = 64
    elf_bytes[ph1 + 40..ph1 + 48].copy_from_slice(&0x200u64.to_le_bytes()); // p_memsz = 512 (BSS = 512 - 64 = 448 bytes)
    elf_bytes[ph1 + 48..ph1 + 56].copy_from_slice(&0x100u64.to_le_bytes()); // p_align = 256 (0x402000 % 0x100 == 0x200 % 0x100 == 0)

    // Parse ELF
    let elf = Elf64File::parse(&elf_bytes).expect("Parse static non-PIE ELF");
    assert_eq!(elf.elf_type, 2);
    assert_eq!(elf.program_headers.len(), 2);

    // Map into virtual address space
    let image = elf.load_image(&elf_bytes, 0).expect("Load ELF image");
    assert_eq!(image.base_address, 0);
    assert_eq!(image.entry_point, 0x401000);
    assert_eq!(image.segments.len(), 2);

    // Check permissions and BSS zeroing
    assert!(image.is_executable(0x401000));
    assert!(!image.is_executable(0x402000));
    // BSS offset 0x402000 + 64 (0x402040) must be 0
    assert_eq!(image.read_byte(0x402040).unwrap(), 0);

    // Verify read-only enforcement on code segment
    let mut mutable_image = image.clone();
    let write_res = mutable_image.write_byte(0x401000, 0x90);
    assert!(write_res.is_err()); // Cannot write to read-only/executable segment!

    // Integrate with Lifter & SMT
    let mut lifter = Lifter::new();
    lifter.load_process_image(&image);
    let extracted = image.extract_code_at(0x401000, 64).expect("Extract code");
    let terms = lifter
        .decode_and_execute_bytes(&extracted, 0x401000)
        .expect("Lift instructions");
    assert_eq!(terms.len(), 3);
    let resolution = lifter.resolve_branch(terms.last().unwrap(), &[]);
    // Target: 0x401000 + 6 + 7 = 0x40100d
    assert_eq!(resolution, BranchResolution::Deterministic(0x40100d));
}

// -----------------------------------------------------------------------------
// Category 2: PIE ELF64 with Load Bias (ET_DYN)
// -----------------------------------------------------------------------------
#[test]
fn test_category2_pie_elf64_with_load_bias() {
    let mut elf_bytes = vec![0u8; 1024];

    elf_bytes[0..4].copy_from_slice(b"\x7fELF");
    elf_bytes[4] = 2; // 64-bit
    elf_bytes[5] = 1; // little-endian
    elf_bytes[6] = 1;

    // e_type = ET_DYN (3: Shared Object / PIE)
    elf_bytes[16..18].copy_from_slice(&3u16.to_le_bytes());
    elf_bytes[18..20].copy_from_slice(&0x3eu16.to_le_bytes());
    // e_entry = 0x1000 (relative to base)
    elf_bytes[24..32].copy_from_slice(&0x1000u64.to_le_bytes());
    elf_bytes[32..40].copy_from_slice(&64u64.to_le_bytes());
    elf_bytes[52..54].copy_from_slice(&64u16.to_le_bytes());
    elf_bytes[54..56].copy_from_slice(&56u16.to_le_bytes());
    elf_bytes[56..58].copy_from_slice(&1u16.to_le_bytes());

    // Payload: mov eax, 1; cmp eax, 1; je +4 (b8 01 00 00 00 83 f8 01 74 04)
    let code = [0xb8, 0x01, 0x00, 0x00, 0x00, 0x83, 0xf8, 0x01, 0x74, 0x04];
    elf_bytes[0x100..0x100 + code.len()].copy_from_slice(&code);

    let ph0 = 64;
    elf_bytes[ph0..ph0 + 4].copy_from_slice(&PT_LOAD.to_le_bytes());
    elf_bytes[ph0 + 4..ph0 + 8].copy_from_slice(&(PF_R | PF_X).to_le_bytes());
    elf_bytes[ph0 + 8..ph0 + 16].copy_from_slice(&0x100u64.to_le_bytes()); // offset = 256
    elf_bytes[ph0 + 16..ph0 + 24].copy_from_slice(&0x1000u64.to_le_bytes()); // vaddr = 0x1000
    elf_bytes[ph0 + 24..ph0 + 32].copy_from_slice(&0x1000u64.to_le_bytes());
    elf_bytes[ph0 + 32..ph0 + 40].copy_from_slice(&0x100u64.to_le_bytes());
    elf_bytes[ph0 + 40..ph0 + 48].copy_from_slice(&0x100u64.to_le_bytes());
    elf_bytes[ph0 + 48..ph0 + 56].copy_from_slice(&0x100u64.to_le_bytes()); // align = 256 (0x1000 % 256 == 0x100 % 256 == 0)

    let elf = Elf64File::parse(&elf_bytes).expect("Parse PIE ELF");
    assert_eq!(elf.elf_type, 3); // ET_DYN

    // Apply load bias: 0x5555_5555_0000
    let bias: u64 = 0x5555_5555_0000;
    let image = elf
        .load_image(&elf_bytes, bias)
        .expect("Load PIE image with bias");
    assert_eq!(image.base_address, bias);
    assert_eq!(image.entry_point, bias + 0x1000);

    // Code is mapped at biased entry point
    assert!(image.is_executable(bias + 0x1000));
    let extracted = image
        .extract_code_at(bias + 0x1000, 64)
        .expect("Extract biased code");
    assert_eq!(&extracted[..code.len()], &code);

    // Lifter resolves branch under bias
    let mut lifter = Lifter::new();
    let terms = lifter
        .decode_and_execute_bytes(&extracted, bias + 0x1000)
        .expect("Lift instructions");
    assert_eq!(terms.len(), 3);
    let resolution = lifter.resolve_branch(terms.last().unwrap(), &[]);
    // Target: (bias + 0x1000) + 10 + 4 = bias + 0x100e
    assert_eq!(resolution, BranchResolution::Deterministic(bias + 0x100e));
}

// -----------------------------------------------------------------------------
// Category 3: PE32+ with Import Directory & IAT
// -----------------------------------------------------------------------------
#[test]
fn test_category3_pe32plus_with_import_directory_and_iat() {
    let mut pe_bytes = vec![0u8; 2048];

    // DOS Header
    pe_bytes[0..2].copy_from_slice(b"MZ");
    pe_bytes[0x3c..0x40].copy_from_slice(&0x80u32.to_le_bytes()); // e_lfanew = 0x80 (128)

    // PE Signature
    let pe_sig = 0x80;
    pe_bytes[pe_sig..pe_sig + 4].copy_from_slice(b"PE\0\0");

    // COFF Header (20 bytes)
    let coff = pe_sig + 4;
    pe_bytes[coff..coff + 2].copy_from_slice(&0x8664u16.to_le_bytes()); // Machine = x86-64
    pe_bytes[coff + 2..coff + 4].copy_from_slice(&2u16.to_le_bytes()); // NumberOfSections = 2 (.text, .idata)
    pe_bytes[coff + 16..coff + 18].copy_from_slice(&240u16.to_le_bytes()); // SizeOfOptionalHeader = 240

    // Optional Header 64 (starts at coff + 20 = 0x98)
    let opt = coff + 20;
    pe_bytes[opt..opt + 2].copy_from_slice(&0x020bu16.to_le_bytes()); // Magic = PE32+
    pe_bytes[opt + 16..opt + 20].copy_from_slice(&0x1000u32.to_le_bytes()); // AddressOfEntryPoint = 0x1000
    pe_bytes[opt + 24..opt + 32].copy_from_slice(&0x140000000u64.to_le_bytes()); // ImageBase = 0x140000000
    pe_bytes[opt + 32..opt + 36].copy_from_slice(&0x1000u32.to_le_bytes()); // SectionAlignment = 0x1000
    pe_bytes[opt + 36..opt + 40].copy_from_slice(&0x200u32.to_le_bytes()); // FileAlignment = 0x200
    pe_bytes[opt + 108..opt + 112].copy_from_slice(&16u32.to_le_bytes()); // NumberOfRvaAndSizes = 16

    // Data Directory 1: IMAGE_DIRECTORY_ENTRY_IMPORT at opt + 112 + 8 = opt + 120
    let import_dir = opt + 112 + 8;
    pe_bytes[import_dir..import_dir + 4].copy_from_slice(&0x2000u32.to_le_bytes()); // Import RVA = 0x2000 (.idata)
    pe_bytes[import_dir + 4..import_dir + 8].copy_from_slice(&64u32.to_le_bytes()); // Import Size = 64

    // Section Table (starts at opt + 240)
    let sec_table = opt + 240;

    // Section 1: .text
    let sec1 = sec_table;
    pe_bytes[sec1..sec1 + 5].copy_from_slice(b".text");
    pe_bytes[sec1 + 8..sec1 + 12].copy_from_slice(&0x100u32.to_le_bytes()); // VirtualSize = 256
    pe_bytes[sec1 + 12..sec1 + 16].copy_from_slice(&0x1000u32.to_le_bytes()); // VirtualAddress = 0x1000
    pe_bytes[sec1 + 16..sec1 + 20].copy_from_slice(&0x200u32.to_le_bytes()); // SizeOfRawData = 512
    pe_bytes[sec1 + 20..sec1 + 24].copy_from_slice(&0x200u32.to_le_bytes()); // PointerToRawData = 512
    pe_bytes[sec1 + 36..sec1 + 40]
        .copy_from_slice(&(IMAGE_SCN_MEM_EXECUTE | IMAGE_SCN_MEM_READ).to_le_bytes());

    // Section 2: .idata (Imports)
    let sec2 = sec_table + 40;
    pe_bytes[sec2..sec2 + 6].copy_from_slice(b".idata");
    pe_bytes[sec2 + 8..sec2 + 12].copy_from_slice(&0x200u32.to_le_bytes()); // VirtualSize = 512
    pe_bytes[sec2 + 12..sec2 + 16].copy_from_slice(&0x2000u32.to_le_bytes()); // VirtualAddress = 0x2000
    pe_bytes[sec2 + 16..sec2 + 20].copy_from_slice(&0x200u32.to_le_bytes()); // SizeOfRawData = 512
    pe_bytes[sec2 + 20..sec2 + 24].copy_from_slice(&0x400u32.to_le_bytes()); // PointerToRawData = 1024
    pe_bytes[sec2 + 36..sec2 + 40]
        .copy_from_slice(&(IMAGE_SCN_MEM_READ | IMAGE_SCN_MEM_WRITE).to_le_bytes());

    // Write .text code at raw offset 0x200 (512):
    // xor eax, eax; jz +5
    let text_code = [0x31, 0xc0, 0x74, 0x05];
    pe_bytes[0x200..0x200 + text_code.len()].copy_from_slice(&text_code);

    // Construct Import Directory Table at raw offset 0x400 (1024, corresponding to RVA 0x2000):
    // Descriptor 0:
    // OriginalFirstThunk RVA = 0x2040 (raw offset 0x440)
    // Name RVA = 0x2080 (raw offset 0x480)
    // FirstThunk RVA = 0x2060 (raw offset 0x460)
    let desc0 = 0x400;
    pe_bytes[desc0..desc0 + 4].copy_from_slice(&0x2040u32.to_le_bytes());
    pe_bytes[desc0 + 12..desc0 + 16].copy_from_slice(&0x2080u32.to_le_bytes());
    pe_bytes[desc0 + 16..desc0 + 20].copy_from_slice(&0x2060u32.to_le_bytes());
    // Descriptor 1: all zeroes (terminator)

    // Name at raw offset 0x480 (RVA 0x2080): "KERNEL32.dll\0"
    let dll_name = b"KERNEL32.dll\0";
    pe_bytes[0x480..0x480 + dll_name.len()].copy_from_slice(dll_name);

    // Thunk at raw offset 0x440 (RVA 0x2040):
    // Import by name: Hint/Name RVA = 0x20a0 (raw offset 0x4a0)
    pe_bytes[0x440..0x448].copy_from_slice(&0x20a0u64.to_le_bytes());
    // Terminating 0 thunk
    pe_bytes[0x448..0x450].copy_from_slice(&0u64.to_le_bytes());

    // Hint/Name entry at raw offset 0x4a0 (RVA 0x20a0): Hint (2 bytes = 0) + Name "ExitProcess\0"
    let func_name = b"\0\0ExitProcess\0";
    pe_bytes[0x4a0..0x4a0 + func_name.len()].copy_from_slice(func_name);

    // Parse PE32+
    let pe = Pe64File::parse(&pe_bytes).expect("Parse PE32+ with imports");
    assert_eq!(pe.image_base, 0x140000000);
    assert_eq!(pe.entry_point_rva, 0x1000);
    assert_eq!(pe.imports.len(), 1);
    assert_eq!(pe.imports[0].dll_name, "KERNEL32.dll");
    assert_eq!(pe.imports[0].functions.len(), 1);
    assert_eq!(
        pe.imports[0].functions[0].name.as_deref(),
        Some("ExitProcess")
    );

    // Map image and verify code execution
    let image = pe.load_image(&pe_bytes, None).expect("Load PE image");
    assert_eq!(image.entry_point, 0x140001000);
    let code_extracted = image
        .extract_code_at(0x140001000, 32)
        .expect("Extract PE code");
    assert_eq!(&code_extracted[..text_code.len()], &text_code);

    let mut lifter = Lifter::new();
    let terms = lifter
        .decode_and_execute_bytes(&code_extracted, 0x140001000)
        .expect("Lift instructions");
    let res = lifter.resolve_branch(terms.last().unwrap(), &[]);
    assert_eq!(res, BranchResolution::Deterministic(0x140001000 + 4 + 5));
}

// -----------------------------------------------------------------------------
// Category 4: PE32+ Relocatable loaded at Rebased ImageBase
// -----------------------------------------------------------------------------
#[test]
fn test_category4_pe32plus_relocatable_rebased_image() {
    let mut pe_bytes = vec![0u8; 2048];

    pe_bytes[0..2].copy_from_slice(b"MZ");
    pe_bytes[0x3c..0x40].copy_from_slice(&0x80u32.to_le_bytes()); // e_lfanew = 0x80

    let pe_sig = 0x80;
    pe_bytes[pe_sig..pe_sig + 4].copy_from_slice(b"PE\0\0");

    let coff = pe_sig + 4;
    pe_bytes[coff..coff + 2].copy_from_slice(&0x8664u16.to_le_bytes()); // x86-64
    pe_bytes[coff + 2..coff + 4].copy_from_slice(&2u16.to_le_bytes()); // 2 sections: .text, .reloc
    pe_bytes[coff + 16..coff + 18].copy_from_slice(&240u16.to_le_bytes());

    let opt = coff + 20;
    pe_bytes[opt..opt + 2].copy_from_slice(&0x020bu16.to_le_bytes());
    pe_bytes[opt + 16..opt + 20].copy_from_slice(&0x1000u32.to_le_bytes()); // Entry = 0x1000
    pe_bytes[opt + 24..opt + 32].copy_from_slice(&0x140000000u64.to_le_bytes()); // Preferred ImageBase = 0x140000000
    pe_bytes[opt + 32..opt + 36].copy_from_slice(&0x1000u32.to_le_bytes());
    pe_bytes[opt + 36..opt + 40].copy_from_slice(&0x200u32.to_le_bytes());
    pe_bytes[opt + 108..opt + 112].copy_from_slice(&16u32.to_le_bytes());

    // Data Directory 5: IMAGE_DIRECTORY_ENTRY_BASERELOC at opt + 112 + 5*8 = opt + 152
    let reloc_dir = opt + 112 + 40;
    pe_bytes[reloc_dir..reloc_dir + 4].copy_from_slice(&0x2000u32.to_le_bytes()); // Reloc RVA = 0x2000 (.reloc)
    pe_bytes[reloc_dir + 4..reloc_dir + 8].copy_from_slice(&12u32.to_le_bytes()); // Reloc Size = 12

    let sec_table = opt + 240;

    // Section 1: .text (RVA 0x1000, raw 0x200, size 0x200)
    let sec1 = sec_table;
    pe_bytes[sec1..sec1 + 5].copy_from_slice(b".text");
    pe_bytes[sec1 + 8..sec1 + 12].copy_from_slice(&0x200u32.to_le_bytes());
    pe_bytes[sec1 + 12..sec1 + 16].copy_from_slice(&0x1000u32.to_le_bytes());
    pe_bytes[sec1 + 16..sec1 + 20].copy_from_slice(&0x200u32.to_le_bytes());
    pe_bytes[sec1 + 20..sec1 + 24].copy_from_slice(&0x200u32.to_le_bytes());
    pe_bytes[sec1 + 36..sec1 + 40].copy_from_slice(
        &(IMAGE_SCN_MEM_EXECUTE | IMAGE_SCN_MEM_READ | IMAGE_SCN_MEM_WRITE).to_le_bytes(),
    );

    // Section 2: .reloc (RVA 0x2000, raw 0x400, size 0x200)
    let sec2 = sec_table + 40;
    pe_bytes[sec2..sec2 + 6].copy_from_slice(b".reloc");
    pe_bytes[sec2 + 8..sec2 + 12].copy_from_slice(&0x200u32.to_le_bytes());
    pe_bytes[sec2 + 12..sec2 + 16].copy_from_slice(&0x2000u32.to_le_bytes());
    pe_bytes[sec2 + 16..sec2 + 20].copy_from_slice(&0x200u32.to_le_bytes());
    pe_bytes[sec2 + 20..sec2 + 24].copy_from_slice(&0x400u32.to_le_bytes());
    pe_bytes[sec2 + 36..sec2 + 40].copy_from_slice(&(IMAGE_SCN_MEM_READ).to_le_bytes());

    // Pointer stored at .text + 0x80 (raw offset 0x280, RVA 0x1080):
    // Preferred address points to 0x140005000
    let preferred_ptr: u64 = 0x140005000;
    pe_bytes[0x280..0x288].copy_from_slice(&preferred_ptr.to_le_bytes());

    // Machine code at raw 0x200 (RVA 0x1000):
    // xor eax, eax; test eax, eax; jz +6
    let code = [0x31, 0xc0, 0x85, 0xc0, 0x74, 0x06];
    pe_bytes[0x200..0x200 + code.len()].copy_from_slice(&code);

    // Build Base Relocation Block at raw 0x400 (RVA 0x2000):
    // PageRVA = 0x1000 (covering .text)
    // BlockSize = 8 (header) + 2 (entry) + 2 (padding) = 12
    let reloc_raw = 0x400;
    pe_bytes[reloc_raw..reloc_raw + 4].copy_from_slice(&0x1000u32.to_le_bytes());
    pe_bytes[reloc_raw + 4..reloc_raw + 8].copy_from_slice(&12u32.to_le_bytes());
    // Entry 0: Type = IMAGE_REL_BASED_DIR64 (10), Offset = 0x080 -> val = (10 << 12) | 0x080 = 0xa080
    let entry_val: u16 = (IMAGE_REL_BASED_DIR64 as u16) << 12 | 0x080;
    pe_bytes[reloc_raw + 8..reloc_raw + 10].copy_from_slice(&entry_val.to_le_bytes());
    // Entry 1: Type = IMAGE_REL_BASED_ABSOLUTE (0) padding
    pe_bytes[reloc_raw + 10..reloc_raw + 12].copy_from_slice(&0u16.to_le_bytes());

    let pe = Pe64File::parse(&pe_bytes).expect("Parse relocatable PE32+");
    assert_eq!(pe.relocations.len(), 1);
    assert_eq!(pe.relocations[0].page_rva, 0x1000);
    assert_eq!(pe.relocations[0].entries.len(), 2);
    assert_eq!(pe.relocations[0].entries[0], (IMAGE_REL_BASED_DIR64, 0x080));

    // Load at rebased image base: 0x240000000 (delta = +0x100000000)
    let new_base: u64 = 0x240000000;
    let image = pe
        .load_image(&pe_bytes, Some(new_base))
        .expect("Rebase and load PE");
    assert_eq!(image.base_address, new_base);
    assert_eq!(image.entry_point, new_base + 0x1000);

    // Verify that pointer at relocated address (new_base + 0x1080) was patched!
    let patched_bytes = image
        .read_bytes(new_base + 0x1080, 8)
        .expect("Read patched pointer");
    let patched_ptr = u64::from_le_bytes([
        patched_bytes[0],
        patched_bytes[1],
        patched_bytes[2],
        patched_bytes[3],
        patched_bytes[4],
        patched_bytes[5],
        patched_bytes[6],
        patched_bytes[7],
    ]);
    let expected_rebased_ptr = preferred_ptr + 0x100000000; // 0x240005000
    assert_eq!(patched_ptr, expected_rebased_ptr);
}
