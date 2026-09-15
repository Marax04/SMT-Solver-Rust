//! Tests for comprehensive PE32+ runtime structures:
//! Export Directory, Exception / Unwind metadata (.pdata), Delay Imports, and TLS Callbacks array.

use smt_solver::binary_loader::Pe64File;

/// Constructs a synthetic PE32+ binary with complete runtime directories:
/// Export Directory (dir 0), Exception Directory (dir 3), TLS (dir 9), and Delay Imports (dir 13).
fn create_comprehensive_pe64_bytes() -> Vec<u8> {
    let mut bytes = vec![0u8; 0x1000]; // 4KB image

    // DOS Header
    bytes[0] = b'M';
    bytes[1] = b'Z';
    bytes[0x3c..0x40].copy_from_slice(&0x80u32.to_le_bytes()); // e_lfanew = 0x80

    // NT Signature at 0x80
    bytes[0x80..0x84].copy_from_slice(b"PE\0\0");

    // COFF Header (20 bytes) at 0x84
    bytes[0x84..0x86].copy_from_slice(&0x8664u16.to_le_bytes()); // AMD64
    bytes[0x86..0x88].copy_from_slice(&2u16.to_le_bytes()); // 2 sections (.text, .rdata)
    bytes[0x94..0x96].copy_from_slice(&240u16.to_le_bytes()); // SizeOfOptionalHeader (240 bytes)

    // Optional Header Standard & Windows fields (offset 0x98)
    bytes[0x98..0x9a].copy_from_slice(&0x020bu16.to_le_bytes()); // PE32+ magic
    bytes[0xa8..0xac].copy_from_slice(&0x1000u32.to_le_bytes()); // AddressOfEntryPoint = 0x1000
    bytes[0xb0..0xb8].copy_from_slice(&0x0000_0001_4000_0000u64.to_le_bytes()); // ImageBase
    bytes[0xb8..0xbc].copy_from_slice(&0x1000u32.to_le_bytes()); // SectionAlignment
    bytes[0xbc..0xc0].copy_from_slice(&0x200u32.to_le_bytes()); // FileAlignment
    bytes[0x104..0x108].copy_from_slice(&16u32.to_le_bytes()); // NumberOfRvaAndSizes = 16

    // Data Directories start at 0x98 + 112 = 0x108:
    // Dir 0: Export Directory (RVA 0x2000, Size 0x100)
    bytes[0x108..0x10c].copy_from_slice(&0x2000u32.to_le_bytes());
    bytes[0x10c..0x110].copy_from_slice(&0x100u32.to_le_bytes());

    // Dir 3: Exception Directory (RVA 0x2100, Size 24 bytes = 2 entries)
    bytes[0x120..0x124].copy_from_slice(&0x2100u32.to_le_bytes());
    bytes[0x124..0x128].copy_from_slice(&24u32.to_le_bytes());

    // Dir 9: TLS Directory (RVA 0x2200, Size 40 bytes)
    bytes[0x150..0x154].copy_from_slice(&0x2200u32.to_le_bytes());
    bytes[0x154..0x158].copy_from_slice(&40u32.to_le_bytes());

    // Dir 13: Delay Import Directory (RVA 0x2300, Size 64 bytes)
    bytes[0x170..0x174].copy_from_slice(&0x2300u32.to_le_bytes());
    bytes[0x174..0x178].copy_from_slice(&64u32.to_le_bytes());

    // Section Table starts at 0x98 + 240 = 0x188
    // Section 1: .text (RVA 0x1000, RawOff 0x200, RawSize 0x200)
    bytes[0x188..0x190].copy_from_slice(b".text\0\0\0");
    bytes[0x190..0x194].copy_from_slice(&0x200u32.to_le_bytes()); // VirtualSize
    bytes[0x194..0x198].copy_from_slice(&0x1000u32.to_le_bytes()); // VirtualAddress
    bytes[0x198..0x19c].copy_from_slice(&0x200u32.to_le_bytes()); // SizeOfRawData
    bytes[0x19c..0x1a0].copy_from_slice(&0x200u32.to_le_bytes()); // PointerToRawData
    bytes[0x1ac..0x1b0].copy_from_slice(&0x60000020u32.to_le_bytes()); // Executable | Readable | Code

    // Section 2: .rdata (RVA 0x2000, RawOff 0x400, RawSize 0x800)
    let s2 = 0x188 + 40;
    bytes[s2..s2 + 8].copy_from_slice(b".rdata\0\0");
    bytes[s2 + 8..s2 + 12].copy_from_slice(&0x800u32.to_le_bytes());
    bytes[s2 + 12..s2 + 16].copy_from_slice(&0x2000u32.to_le_bytes()); // VirtualAddress = 0x2000
    bytes[s2 + 16..s2 + 20].copy_from_slice(&0x800u32.to_le_bytes());
    bytes[s2 + 20..s2 + 24].copy_from_slice(&0x400u32.to_le_bytes()); // PointerToRawData = 0x400
    bytes[s2 + 36..s2 + 40].copy_from_slice(&0x40000040u32.to_le_bytes()); // Initialized data | Readable

    // Populate .rdata payload at raw offset 0x400 (corresponds to RVA 0x2000):

    // 1. Export Directory at RVA 0x2000 -> raw offset 0x400
    // OrdinalBase = 1
    bytes[0x410..0x414].copy_from_slice(&1u32.to_le_bytes());
    // NumberOfFunctions = 1
    bytes[0x414..0x418].copy_from_slice(&1u32.to_le_bytes());
    // NumberOfNames = 1
    bytes[0x418..0x41c].copy_from_slice(&1u32.to_le_bytes());
    // AddressOfFunctions = RVA 0x2050 -> offset 0x450
    bytes[0x41c..0x420].copy_from_slice(&0x2050u32.to_le_bytes());
    // AddressOfNames = RVA 0x2060 -> offset 0x460
    bytes[0x420..0x424].copy_from_slice(&0x2060u32.to_le_bytes());
    // AddressOfNameOrdinals = RVA 0x2070 -> offset 0x470
    bytes[0x424..0x428].copy_from_slice(&0x2070u32.to_le_bytes());

    // Export Function 0 RVA at offset 0x450: points to EntryPoint 0x1000
    bytes[0x450..0x454].copy_from_slice(&0x1000u32.to_le_bytes());
    // Export Name Pointer at offset 0x460: points to RVA 0x2080 -> offset 0x480
    bytes[0x460..0x464].copy_from_slice(&0x2080u32.to_le_bytes());
    // Export Ordinal at offset 0x470: index 0
    bytes[0x470..0x472].copy_from_slice(&0u16.to_le_bytes());
    // Export Name ASCII at offset 0x480: "SuperExportFunction\0"
    bytes[0x480..0x480 + 20].copy_from_slice(b"SuperExportFunction\0");

    // 2. Exception Directory at RVA 0x2100 -> raw offset 0x500
    // Entry 1: [0x1000..0x1050, unwind: 0x2150]
    bytes[0x500..0x504].copy_from_slice(&0x1000u32.to_le_bytes());
    bytes[0x504..0x508].copy_from_slice(&0x1050u32.to_le_bytes());
    bytes[0x508..0x50c].copy_from_slice(&0x2150u32.to_le_bytes());
    // Entry 2: [0x1050..0x1100, unwind: 0x2160]
    bytes[0x50c..0x510].copy_from_slice(&0x1050u32.to_le_bytes());
    bytes[0x510..0x514].copy_from_slice(&0x1100u32.to_le_bytes());
    bytes[0x514..0x518].copy_from_slice(&0x2160u32.to_le_bytes());

    // 3. TLS Directory at RVA 0x2200 -> raw offset 0x600
    // AddressOfCallbacks = ImageBase + RVA 0x2250 = 0x0000_0001_4000_2250
    let cb_va = 0x0000_0001_4000_0000u64 + 0x2250u64;
    bytes[0x618..0x620].copy_from_slice(&cb_va.to_le_bytes());
    // TLS Callbacks table at RVA 0x2250 -> raw offset 0x650
    // 2 callbacks then null: 0x140001010, 0x140001020, 0
    let cb1 = 0x0000_0001_4000_1010u64;
    let cb2 = 0x0000_0001_4000_1020u64;
    bytes[0x650..0x658].copy_from_slice(&cb1.to_le_bytes());
    bytes[0x658..0x660].copy_from_slice(&cb2.to_le_bytes());
    bytes[0x660..0x668].copy_from_slice(&0u64.to_le_bytes());

    // 4. Delay Import Directory at RVA 0x2300 -> raw offset 0x700
    // Name RVA at +4 = 0x2350 -> offset 0x750
    bytes[0x704..0x708].copy_from_slice(&0x2350u32.to_le_bytes());
    // INT RVA at +16 = 0x2360 -> offset 0x760
    bytes[0x710..0x714].copy_from_slice(&0x2360u32.to_le_bytes());
    // Delay DLL name at offset 0x750: "crypt32.dll\0"
    bytes[0x750..0x750 + 12].copy_from_slice(b"crypt32.dll\0");
    // Thunk at offset 0x760: Hint/Name RVA 0x2380 -> offset 0x780
    bytes[0x760..0x768].copy_from_slice(&0x2380u64.to_le_bytes());
    bytes[0x768..0x770].copy_from_slice(&0u64.to_le_bytes()); // Null terminator
                                                              // Hint/Name at offset 0x780: Hint 0, Name "CryptProtectData\0"
    bytes[0x780..0x782].copy_from_slice(&0u16.to_le_bytes());
    bytes[0x782..0x782 + 17].copy_from_slice(b"CryptProtectData\0");

    bytes
}

#[test]
fn test_pe64_runtime_complete_metadata_parsing() {
    let raw = create_comprehensive_pe64_bytes();
    let pe = Pe64File::parse(&raw).expect("Valid comprehensive PE64 binary");

    // 1. Verify Export Directory
    assert_eq!(pe.exports.len(), 1);
    let exp = &pe.exports[0];
    assert_eq!(exp.name.as_deref(), Some("SuperExportFunction"));
    assert_eq!(exp.ordinal, 1);
    assert_eq!(exp.rva, 0x1000);
    assert!(exp.forwarder.is_none());

    // 2. Verify Exception / Unwind (.pdata) Directory
    assert_eq!(pe.exception_directory.len(), 2);
    assert_eq!(pe.exception_directory[0].begin_address, 0x1000);
    assert_eq!(pe.exception_directory[0].end_address, 0x1050);
    assert_eq!(pe.exception_directory[0].unwind_info_address, 0x2150);

    assert_eq!(pe.exception_directory[1].begin_address, 0x1050);
    assert_eq!(pe.exception_directory[1].end_address, 0x1100);
    assert_eq!(pe.exception_directory[1].unwind_info_address, 0x2160);

    // 3. Verify TLS Callbacks Array
    assert!(pe.tls.is_some());
    let tls = pe.tls.as_ref().unwrap();
    assert_eq!(tls.callbacks.len(), 2);
    assert_eq!(tls.callbacks[0], 0x0000_0001_4000_1010);
    assert_eq!(tls.callbacks[1], 0x0000_0001_4000_1020);

    // 4. Verify Delay Imports
    assert_eq!(pe.delay_imports.len(), 1);
    let d_imp = &pe.delay_imports[0];
    assert_eq!(d_imp.dll_name, "crypt32.dll");
    assert_eq!(d_imp.functions.len(), 1);
    assert_eq!(d_imp.functions[0].name.as_deref(), Some("CryptProtectData"));
    assert!(d_imp.functions[0].ordinal.is_none());
}
