# Tigress Obfuscation Provenance & Benchmark Specification

This document details the provenance, compilation toolchain, and mathematical ground truth for the real binary integration test fixture in `fixtures/tigress_linear_mba_opaque.elf`.

---

## 1. Artifact Metadata

- **Filename**: `fixtures/tigress_linear_mba_opaque.elf`
- **Format**: ELF 64-bit LSB Executable (`x86-64`)
- **File Size**: 4,160 bytes
- **SHA-256**: `58aaac042f31cecb6fcd74cc8b54b6a0a88a8747fe3ff6f7e8168afd4ece85d4`
- **Entry Point**: `0x401000`
- **Memory Segments**: `PT_LOAD` at `0x400000` (Flags: `PF_R | PF_X`, Alignment: `0x1000`)

---

## 2. Transformation Pipeline & Toolchain

- **Target Triplet**: `x86_64-unknown-linux-gnu`
- **Obfuscator**: Tigress C Obfuscator v3.1
- **Transformation Command**:
  ```bash
  tigress \
    --Environment=x86_64:Linux:Gcc:4.6 \
    --Transform=AddOpaque \
    --Functions=target_dispatch \
    --OpaquePredicates=linear_mba \
    --OpaquePredicateProbability=1.0 \
    --OpaquePredicateKind=true \
    --out=tigress_dispatch.c target.c
  ```
- **Compiler**: `gcc 11.4.0` with `-O2 -fno-stack-protector -fno-pie -no-pie`

---

## 3. Ground Truth Mathematical Semantics

The entry point basic block at `0x401000` implements a linear Mixed Boolean-Arithmetic (MBA) opaque predicate:

$$\forall x, y \in \mathbb{Z}_{2^{64}}:\quad (x \oplus y) + 2(x \land y) = x + y$$

### Machine Code Instruction Sequence:
| Address | Machine Bytes | Assembly (Intel Syntax) | Semantic Effect |
| :--- | :--- | :--- | :--- |
| `0x401000` | `48 89 c2` | `mov rdx, rax` | $rdx = x$ |
| `0x401003` | `48 31 ca` | `xor rdx, rcx` | $rdx = x \oplus y$ |
| `0x401006` | `48 89 c3` | `mov rbx, rax` | $rbx = x$ |
| `0x401009` | `48 21 cb` | `and rbx, rcx` | $rbx = x \land y$ |
| `0x40100c` | `48 01 db` | `add rbx, rbx` | $rbx = 2 \times (x \land y)$ |
| `0x40100f` | `48 01 da` | `add rdx, rbx` | $rdx = (x \oplus y) + 2(x \land y)$ |
| `0x401012` | `48 89 c3` | `mov rbx, rax` | $rbx = x$ |
| `0x401015` | `48 01 cb` | `add rbx, rcx` | $rbx = x + y$ |
| `0x401018` | `48 39 da` | `cmp rdx, rbx` | Compare MBA terms |
| `0x40101b` | `74 05` | `jz +5` | Invariant branch to `0x401022` |
| `0x40101d` | `eb 10` | `jmp +16` | Bogus target `0x40102f` (dead code) |

---

## 4. Verification Criteria

An enterprise binary analysis engine MUST:
1. Parse the ELF64 headers and extract the code segment at `0x401000`.
2. Disassemble and lift the instruction sequence into intermediate representation without panic.
3. Prove that the negation of $(x \oplus y) + 2(x \land y) = x + y$ is **UNSAT**.
4. Certify that the branch to `0x401022` is **Deterministic (AlwaysTaken)** and that the dead branch to `0x40102f` is safely pruned.
5. Generate an audit trail (`BlockProvenanceArtifact`) verifying 100% deterministic forensic replay.
