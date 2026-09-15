# Changelog

All notable changes to this project are documented in this file in accordance with [Keep a Changelog](https://keepachangelog.com/en/1.0.0/).

---

## [1.0.0] - 2026-09-15 — Enterprise v1.0 Production Release

### Added
- **Independent DRAT Proof Certificate Verification**:
  - Full algorithmic Reverse Unit Propagation (RUP) checking via `smt_sat::DratChecker`.
  - Independent verification of learned and deleted clauses terminating in the empty clause (`0`), establishing mathematical proof of unsatisfiability.
  - Recording of `ProofCertificateCheckResult` alongside `DoubleCheckResult` in `BlockProvenanceArtifact`.
- **Coverage-Guided Fuzzing Infrastructure**:
  - `cargo-fuzz` targets (`fuzz_x86_decoder`, `fuzz_smt_parser`, `fuzz_qf_bv_diff`) with persistent seed corpora in `fuzz/corpus/`.
  - Continuous regression corpus management and fuzz harness integration.
- **Real Compiled Tigress / OLLVM Binary Fixtures**:
  - Added `fixtures/tigress_linear_mba_opaque.elf` compiled with `x86_64-unknown-linux-gnu-gcc 11.4.0` under Tigress v3.1 (`--Transform=AddOpaque --OpaquePredicates=linear_mba`).
  - Added complete cryptographic provenance documentation in `fixtures/TIGRESS_PROVENANCE.md`.
  - Added end-to-end integration test `real_tigress_binary_e2e_test.rs` asserting binary loading, disassembly, symbolic lifting, MBA refutation, and deterministic replay.
- **Supply Chain Hygiene & SBOM**:
  - Generated complete CycloneDX 1.5 JSON SBOM (`sbom.cyclonedx.json`) with cryptographic SHA-256 hashes and license clearances.
  - Comprehensive `cargo-deny` configuration (`deny.toml`) enforcing MIT/Apache-2.0 licenses and zero advisory vulnerabilities.
- **Public Transparent Benchmarks**:
  - Published `BENCHMARKS.md` detailing empirical performance comparisons with Z3 4.12 and cvc5 1.1 across specialized MBA/QF_BV and general SMT-LIB theories.
- **Release Readiness Sign-Off**:
  - Updated `RELEASE_READINESS_CHECKLIST.md` with explicit signed-off quality gates, rollback protocol, and audit logs.
- **API Stability Contract**:
  - Published `API_STABILITY.md` detailing SemVer commitments and crate stability tiers.

### Changed
- Workspace version bumped from `0.1.0` to `1.0.0`.
- Typed error propagation unified across `DecoderError`, `LifterError`, and `LoaderError`.
- `ReplayEngine` enhanced to support dual formula/binary hash matching for standalone basic blocks and full ELF/PE images.
- Doctest coverage significantly expanded across all public crate APIs.

---

## [0.1.0-rc1] - 2026-09-15 — Release Candidate 1

### Added
- Unified `ResourceLimits` configuration (timeout, memory budget, AST depth, store chain limit, conflict limit).
- Persistent disk cache (`PersistentCache`) keyed by formula SHA-256 with concurrent lock safety.
- Explainability engine (`DeobfuscationExplainer`) generating human-readable deobfuscation narratives.
- Deterministic replay engine (`ReplayEngine`) for verification of provenance artifacts.
- Enterprise CLI commands: `--analyze-bin`, `--audit-dir`, `--replay`, `--explain`, `--cache-dir`.
- Strict memory coherence test suite (`memory_coherence_tests.rs`).

---

## [0.1.0-beta.11] - 2026-09-15
- Hardened ELF64/PE32+ loaders: segment load bias, PIE base randomization, alignment congruence, import/relocation parsing.
- Sound memory semantics with layered address spaces and permission checking.
- Opaque predicate refutation on MBA-protected basic blocks.
