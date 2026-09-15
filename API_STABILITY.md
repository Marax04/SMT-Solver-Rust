# SMT-Solver-Rust: API Stability & Compatibility Specification

**Release Version**: 1.0.0  
**Effective Date**: September 2026  
**Status**: Certified Enterprise Stable  

---

## 1. SemVer 2.0.0 Commitments

SMT-Solver-Rust follows strict [Semantic Versioning 2.0.0](https://semver.org/).
For version `MAJOR.MINOR.PATCH`:
- **MAJOR**: Breaking changes to Tier 1 public interfaces, data types, or command-line flags.
- **MINOR**: Backward-compatible new features, new theory solvers, new AST node types, performance optimizations, or expanded instruction decoders.
- **PATCH**: Backward-compatible bug fixes, security remediations, and internal documentation improvements.

---

## 2. Workspace Crate Classification & Stability Tiers

| Crate | Stability Tier | SemVer Guarantee | Primary Target Audience |
| :--- | :---: | :---: | :--- |
| `smt-api` | **Tier 1 (Stable)** | Breaking changes only in Major releases. Fully stabilized C-FFI and high-level Rust bindings. | External integrations, IDA Pro / Ghidra plugins, Python/C FFI bindings. |
| `smt-solver` | **Tier 1 (Stable)** | Stable pipeline API (`Lifter`, `DeobfuscationExplainer`, `ReplayEngine`, `PersistentCache`). | Binary analysis pipelines, automated deobfuscators, symbolic engines. |
| `smt-core` | **Tier 1 (Stable)** | Stable AST (`Term`, `Sort`, `TermPool`, `Model`). | Tool builders constructing custom symbolic terms. |
| `smt-mba` | **Tier 1 (Stable)** | Stable MBA simplifier interface (`LinearMbaSimplifier`, `Gf2LinearSolver`). | Obfuscation researchers, algebraic simplification tools. |
| `smt-sat` | **Tier 1 (Stable)** | Stable CDCL API (`SatSolver`, `DratChecker`, `Lit`, `Var`). | Solvers, theorem proving components, proof verifiers. |
| `smt-parser` | **Tier 1 (Stable)** | Standard SMT-LIB 2.6 syntax parser conformance. | SMT benchmark runners and interactive tools. |
| `smt-cli` | **Tier 2 (Tooling)** | Command-line interface with guaranteed flag backward-compatibility for major flags (`--analyze-bin`, `--replay`, `--explain`, `--audit-dir`, `--cache-dir`). | End users, automated CI/CD security pipelines. |
| `smt-theories` | **Tier 2 (Plumbing)** | Internal theory solver engines (Simplex, BitBlaster, EUF congruence closure). | SMT engine internals. May be refactored across minor versions. |
| `smt-preprocess`| **Tier 2 (Plumbing)** | Internal formula simplifiers and preprocessors. | SMT engine internals. |

---

## 3. Backward Compatibility & Deprecation Policy

1. **Deprecation Window**: Any public API scheduled for removal will be marked with `#[deprecated(since = "1.X.0", note = "...")]` at least one minor release prior to removal in the next major version.
2. **Deterministic Artifact Compatibility**:
   - Deobfuscation audit trail artifacts (`*.provenance.json` and `*.provenance.md`) produced by version 1.0.0 are guaranteed to be replayable by all future 1.x releases of `ReplayEngine`.
   - The JSON schema for `BlockProvenanceArtifact` will only add optional fields in minor versions; existing fields will never be removed or renamed in 1.x.
3. **Resource Limit Safety**: `ResourceLimits` default values are tuned for safety and will never become unbounded in minor versions.
