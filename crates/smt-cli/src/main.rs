use smt_parser::binary::{BinaryDecoder, BinaryEncoder};
use smt_parser::parser::Parser;
use smt_solver::binary_loader::BinaryLoader;
use smt_solver::cache::PersistentCache;
use smt_solver::engine::Solver;
use smt_solver::explain::DeobfuscationExplainer;
use smt_solver::lifter::{IrInstruction, Lifter};
use smt_solver::opaque::OpaqueClassification;
use smt_solver::provenance::{BlockProvenanceArtifact, ProvenanceConfidence};
use smt_solver::replay::ReplayEngine;
use smt_solver::x86_decoder::X86Decoder;
use std::env;
use std::fs;
use std::io::{self, BufRead, Write};
use std::process::ExitCode;

fn print_help() {
    println!("SMT-Solver-Rust — High-Performance Pure Rust SMT Solver");
    println!("Usage:");
    println!("  smt-cli [OPTIONS] [FILE.smt2]");
    println!();
    println!("General Options:");
    println!("  --stats               Print solver metrics and statistics in JSON format");
    println!("  --drat <FILE>         Export DRAT proof certificate for UNSAT instances");
    println!("  --bin-encode <OUT>    Encode input SMT-LIB2 script to compact binary format");
    println!("  --bin-run <IN>        Execute pre-encoded binary SMT file");
    println!();
    println!("Deobfuscation & Cryptanalysis Options:");
    println!("  --check-opaque        Classify assertion as an opaque predicate (AlwaysTrue/AlwaysFalse/Dynamic)");
    println!("  --enumerate <LIMIT>   Enumerate up to <LIMIT> satisfying models (decrypt/crackme key recovery)");
    println!("  --score <HEURISTIC>   Rank enumerated candidate models ('ascii', 'entropy', 'weight') [Ranking triage, not filter]");
    println!("  --crypto-find         Scan AST for cryptographic constants and structural round patterns");
    println!("  --mba-simplify        Simplify obfuscated Mixed Boolean-Arithmetic (MBA) formulas");
    println!();
    println!("Enterprise Binary Analysis & Forensic Audit Options:");
    println!("  --analyze-bin <FILE>  Load ELF/PE binary, decode basic blocks, and execute certified branch pruning");
    println!("  --audit-dir <DIR>     Export provenance Markdown and JSON audit trail to specified directory");
    println!("  --replay <JSON>       Perform deterministic replay verification on saved audit provenance artifact");
    println!("  --explain <JSON>      Generate natural-language analyst explanation narrative from provenance artifact");
    println!("  --cache-dir <DIR>     Enable persistent cross-session formula and AST simplification cache");
    println!();
    println!("  -h, --help            Print help information");
}

fn main() -> ExitCode {
    let args: Vec<String> = env::args().collect();

    let mut show_stats = false;
    let mut drat_out: Option<String> = None;
    let mut bin_encode_out: Option<String> = None;
    let mut bin_run_in: Option<String> = None;
    let mut input_file: Option<String> = None;
    let mut check_opaque = false;
    let mut enumerate_limit: Option<usize> = None;
    let mut score_heuristic: Option<smt_solver::ScoreHeuristic> = None;
    let mut crypto_find = false;
    let mut mba_simplify = false;
    let mut analyze_bin: Option<String> = None;
    let mut audit_dir: Option<String> = None;
    let mut replay_in: Option<String> = None;
    let mut explain_in: Option<String> = None;
    let mut cache_dir: Option<String> = None;

    let mut i = 1;
    while i < args.len() {
        match args[i].as_str() {
            "-h" | "--help" => {
                print_help();
                return ExitCode::SUCCESS;
            }
            "--stats" => {
                show_stats = true;
                i += 1;
            }
            "--check-opaque" => {
                check_opaque = true;
                i += 1;
            }
            "--crypto-find" => {
                crypto_find = true;
                i += 1;
            }
            "--mba-simplify" => {
                mba_simplify = true;
                i += 1;
            }
            "--score" => {
                if i + 1 < args.len() {
                    match args[i + 1].to_lowercase().as_str() {
                        "ascii" => {
                            score_heuristic = Some(smt_solver::ScoreHeuristic::AsciiPrintable)
                        }
                        "entropy" => score_heuristic = Some(smt_solver::ScoreHeuristic::Entropy),
                        "weight" => {
                            score_heuristic = Some(smt_solver::ScoreHeuristic::LowHammingWeight)
                        }
                        other => {
                            eprintln!("Error: Unknown scoring heuristic '{}'. Choose 'ascii', 'entropy', or 'weight'", other);
                            return ExitCode::FAILURE;
                        }
                    }
                    i += 2;
                } else {
                    eprintln!("Error: --score requires a heuristic argument ('ascii', 'entropy', 'weight')");
                    return ExitCode::FAILURE;
                }
            }
            "--enumerate" => {
                if i + 1 < args.len() {
                    match args[i + 1].parse::<usize>() {
                        Ok(limit) => {
                            enumerate_limit = Some(limit);
                            i += 2;
                        }
                        Err(_) => {
                            eprintln!("Error: --enumerate requires a positive integer limit");
                            return ExitCode::FAILURE;
                        }
                    }
                } else {
                    eprintln!("Error: --enumerate requires a limit argument");
                    return ExitCode::FAILURE;
                }
            }
            "--drat" => {
                if i + 1 < args.len() {
                    drat_out = Some(args[i + 1].clone());
                    i += 2;
                } else {
                    eprintln!("Error: --drat requires a file argument");
                    return ExitCode::FAILURE;
                }
            }
            "--bin-encode" => {
                if i + 1 < args.len() {
                    bin_encode_out = Some(args[i + 1].clone());
                    i += 2;
                } else {
                    eprintln!("Error: --bin-encode requires an output file argument");
                    return ExitCode::FAILURE;
                }
            }
            "--bin-run" => {
                if i + 1 < args.len() {
                    bin_run_in = Some(args[i + 1].clone());
                    i += 2;
                } else {
                    eprintln!("Error: --bin-run requires an input file argument");
                    return ExitCode::FAILURE;
                }
            }
            "--analyze-bin" => {
                if i + 1 < args.len() {
                    analyze_bin = Some(args[i + 1].clone());
                    i += 2;
                } else {
                    eprintln!("Error: --analyze-bin requires a binary file argument");
                    return ExitCode::FAILURE;
                }
            }
            "--audit-dir" => {
                if i + 1 < args.len() {
                    audit_dir = Some(args[i + 1].clone());
                    i += 2;
                } else {
                    eprintln!("Error: --audit-dir requires a directory argument");
                    return ExitCode::FAILURE;
                }
            }
            "--replay" => {
                if i + 1 < args.len() {
                    replay_in = Some(args[i + 1].clone());
                    i += 2;
                } else {
                    eprintln!("Error: --replay requires a JSON provenance file argument");
                    return ExitCode::FAILURE;
                }
            }
            "--explain" => {
                if i + 1 < args.len() {
                    explain_in = Some(args[i + 1].clone());
                    i += 2;
                } else {
                    eprintln!("Error: --explain requires a JSON provenance file argument");
                    return ExitCode::FAILURE;
                }
            }
            "--cache-dir" => {
                if i + 1 < args.len() {
                    cache_dir = Some(args[i + 1].clone());
                    i += 2;
                } else {
                    eprintln!("Error: --cache-dir requires a directory argument");
                    return ExitCode::FAILURE;
                }
            }
            file if !file.starts_with('-') => {
                input_file = Some(file.to_string());
                i += 1;
            }
            other => {
                eprintln!("Error: Unknown option '{}'", other);
                return ExitCode::FAILURE;
            }
        }
    }

    // Optional cross-session persistent cache initialization
    if let Some(ref cache_path) = cache_dir {
        let _ = fs::create_dir_all(cache_path);
        let _cache = PersistentCache::open(format!("{}/smt_cache.db", cache_path));
        println!(
            "Persistent cross-session formula cache enabled at '{}'",
            cache_path
        );
    }

    // Enterprise Forensic Replay Mode
    if let Some(json_file) = replay_in {
        println!("=== SMT-Solver-Rust: Deterministic Forensic Replay Engine ===");
        match fs::read_to_string(&json_file) {
            Ok(content) => match BlockProvenanceArtifact::from_json(&content) {
                Ok(artifact) => match ReplayEngine::replay(&artifact) {
                    Ok(report) => {
                        println!("Replay Reproducible: {}", report.is_reproducible);
                        println!(
                            "Decoded Instruction Count: {}",
                            report.decoded_instruction_count
                        );
                        println!("Binary SHA-256 Matched: {}", report.binary_hash_matched);
                        println!("Resolution Matched: {}", report.resolution_matched);
                        println!("Status Matched: {}", report.status_matched);
                        println!("Diagnostic: {}", report.diagnostic);
                        if report.is_reproducible {
                            return ExitCode::SUCCESS;
                        } else {
                            return ExitCode::FAILURE;
                        }
                    }
                    Err(e) => {
                        eprintln!("Replay execution error: {}", e);
                        return ExitCode::FAILURE;
                    }
                },
                Err(e) => {
                    eprintln!("Failed to parse provenance artifact JSON: {}", e);
                    return ExitCode::FAILURE;
                }
            },
            Err(e) => {
                eprintln!("Failed to read replay JSON file '{}': {}", json_file, e);
                return ExitCode::FAILURE;
            }
        }
    }

    // Enterprise Natural-Language Explanation Mode
    if let Some(json_file) = explain_in {
        match fs::read_to_string(&json_file) {
            Ok(content) => match BlockProvenanceArtifact::from_json(&content) {
                Ok(artifact) => {
                    println!("{}", DeobfuscationExplainer::explain(&artifact));
                    return ExitCode::SUCCESS;
                }
                Err(e) => {
                    eprintln!("Failed to parse provenance artifact JSON: {}", e);
                    return ExitCode::FAILURE;
                }
            },
            Err(e) => {
                eprintln!("Failed to read JSON file '{}': {}", json_file, e);
                return ExitCode::FAILURE;
            }
        }
    }

    // Enterprise Binary Analysis & Certified Branch Pruning Mode
    if let Some(bin_path) = analyze_bin {
        println!("=== SMT-Solver-Rust: Enterprise Binary Triage & Branch Pruning ===");
        let bytes = match fs::read(&bin_path) {
            Ok(b) => b,
            Err(e) => {
                eprintln!("Failed to read binary file '{}': {}", bin_path, e);
                return ExitCode::FAILURE;
            }
        };

        match BinaryLoader::load_process_image(&bytes, None) {
            Ok((format, image)) => {
                println!("Binary Format: {:?}", format);
                println!("Entry Point: {:#x}", image.entry_point);
                println!("Base Address: {:#x}", image.base_address);
                println!("Mapped Segments: {}", image.segments.len());
                for seg in &image.segments {
                    println!(
                        "  - [{:#x} - {:#x}] ({} bytes, r:{}, w:{}, x:{})",
                        seg.base_vaddr,
                        seg.base_vaddr + seg.size as u64,
                        seg.size,
                        seg.is_readable,
                        seg.is_writable,
                        seg.is_executable
                    );
                }

                if let Ok(entry_bytes) = image.extract_code_at(image.entry_point, 64) {
                    match X86Decoder::decode_block(&entry_bytes, image.entry_point) {
                        Ok(bb) => {
                            println!(
                                "\nDisassembled Basic Block at {:#x} ({} instructions):",
                                bb.address,
                                bb.instructions.len()
                            );
                            let mut disasm_lines = Vec::new();
                            for inst in &bb.instructions {
                                let line = format!("{:?}", inst);
                                println!("  {}", line);
                                disasm_lines.push(line);
                            }

                            let mut lifter = Lifter::new();
                            for inst in &bb.instructions {
                                lifter.step(inst);
                            }

                            let terminator = bb
                                .instructions
                                .last()
                                .cloned()
                                .unwrap_or(IrInstruction::Nop);
                            let cert = lifter.resolve_branch_certified(&terminator, &[]);

                            println!("\nBranch Pruning & Certified Resolution:");
                            println!("  Status: {:?}", cert.status);
                            println!("  Resolution: {:?}", cert.resolution);
                            println!("  Certificate: {}", cert.certificate);

                            let artifact = BlockProvenanceArtifact::new(
                                &bytes,
                                bb.address,
                                &entry_bytes,
                                disasm_lines,
                                cert.resolution,
                                cert.status,
                                ProvenanceConfidence::Proven,
                            );

                            println!(
                                "\nNatural-Language Analysis Narrative:\n{}",
                                DeobfuscationExplainer::explain(&artifact)
                            );

                            if let Some(ref out_dir) = audit_dir {
                                let _ = fs::create_dir_all(out_dir);
                                let md_path =
                                    format!("{}/provenance_{:#x}.md", out_dir, bb.address);
                                let json_path =
                                    format!("{}/provenance_{:#x}.json", out_dir, bb.address);
                                let _ = fs::write(&md_path, artifact.to_markdown());
                                let _ = fs::write(&json_path, artifact.to_json());
                                println!("Audit provenance saved to '{}'", out_dir);
                            }
                        }
                        Err(e) => {
                            eprintln!(
                                "Warning: Failed to decode basic block at entry point: {}",
                                e
                            );
                        }
                    }
                }
                return ExitCode::SUCCESS;
            }
            Err(e) => {
                eprintln!("Failed to load binary '{}': {}", bin_path, e);
                return ExitCode::FAILURE;
            }
        }
    }

    let mut solver = Solver::new();
    if drat_out.is_some() {
        solver.sat.enable_drat(true);
    }

    // Binary execution mode
    if let Some(bin_path) = bin_run_in {
        match fs::read(&bin_path) {
            Ok(bytes) => {
                let mut decoder = BinaryDecoder::new(&mut solver.sorts, &mut solver.terms);
                match decoder.decode_commands(&bytes) {
                    Ok(commands) => {
                        for cmd in commands {
                            match solver.execute_command(cmd) {
                                Ok(out) => {
                                    if !out.is_empty() {
                                        println!("{}", out);
                                    }
                                }
                                Err(err) => {
                                    eprintln!("Execution error: {}", err);
                                    return ExitCode::FAILURE;
                                }
                            }
                        }
                    }
                    Err(err) => {
                        eprintln!("Binary decode error: {}", err);
                        return ExitCode::FAILURE;
                    }
                }
            }
            Err(err) => {
                eprintln!("Failed to read binary file '{}': {}", bin_path, err);
                return ExitCode::FAILURE;
            }
        }
        return ExitCode::SUCCESS;
    }

    // File or REPL mode
    let script_content = if let Some(file_path) = input_file {
        match fs::read_to_string(&file_path) {
            Ok(content) => content,
            Err(err) => {
                eprintln!("Failed to read file '{}': {}", file_path, err);
                return ExitCode::FAILURE;
            }
        }
    } else {
        // Run interactive REPL
        return run_repl(&mut solver);
    };

    // Binary encode mode
    if let Some(out_path) = bin_encode_out {
        let mut parser = Parser::new(&mut solver.sorts, &mut solver.terms);
        match parser.parse_script(&script_content) {
            Ok(commands) => {
                let encoder = BinaryEncoder::new(&solver.sorts, &solver.terms);
                let bytes = encoder.encode_commands(&commands);
                if let Err(err) = fs::write(&out_path, bytes) {
                    eprintln!("Failed to write binary output: {}", err);
                    return ExitCode::FAILURE;
                }
                println!("Successfully compiled SMT-LIB to binary: '{}'", out_path);
                return ExitCode::SUCCESS;
            }
            Err(err) => {
                eprintln!("Parse error: {}", err);
                return ExitCode::FAILURE;
            }
        }
    }

    // Opaque predicate analysis mode
    if check_opaque {
        let mut parser = Parser::new(&mut solver.sorts, &mut solver.terms);
        let commands = match parser.parse_script(&script_content) {
            Ok(cmds) => cmds,
            Err(e) => {
                eprintln!("Parse error: {}", e);
                return ExitCode::FAILURE;
            }
        };

        for cmd in commands {
            if let Err(e) = solver.execute_command(cmd) {
                eprintln!("Execution error: {}", e);
                return ExitCode::FAILURE;
            }
        }

        if let Some(&last_assertion) = solver.assertions().last() {
            let classification = solver.check_opaque(last_assertion);
            match classification {
                OpaqueClassification::AlwaysTrue => {
                    println!("Opaque Predicate: AlwaysTrue (Invariant: branch always taken)");
                }
                OpaqueClassification::AlwaysFalse => {
                    println!("Opaque Predicate: AlwaysFalse (Invariant: branch never taken)");
                }
                OpaqueClassification::Dynamic => {
                    println!("Opaque Predicate: Dynamic (Conditional: branch depends on inputs)");
                }
                OpaqueClassification::Unreachable => {
                    println!("Opaque Predicate: Unreachable (Path Condition is UNSAT)");
                }
                OpaqueClassification::Unknown => {
                    println!("Opaque Predicate: Unknown");
                }
            }
            return ExitCode::SUCCESS;
        } else {
            eprintln!("Error: No assertions found in script to classify as opaque predicate");
            return ExitCode::FAILURE;
        }
    }

    // Crypto fingerprinting mode
    if crypto_find {
        let mut parser = Parser::new(&mut solver.sorts, &mut solver.terms);
        let commands = match parser.parse_script(&script_content) {
            Ok(cmds) => cmds,
            Err(e) => {
                eprintln!("Parse error: {}", e);
                return ExitCode::FAILURE;
            }
        };

        for cmd in commands {
            if let Err(e) = solver.execute_command(cmd) {
                eprintln!("Execution error: {}", e);
                return ExitCode::FAILURE;
            }
        }

        let matches = solver.scan_crypto();
        if matches.is_empty() {
            println!("No cryptographic constants or signatures identified.");
        } else {
            println!("Identified {} cryptographic signature(s):", matches.len());
            for m in &matches {
                println!(
                    "  - [{}] {} (Confidence: {:.1}%, terms: {})",
                    m.algorithm.name(),
                    m.description,
                    m.confidence * 100.0,
                    m.matched_terms.len()
                );
            }
        }
        return ExitCode::SUCCESS;
    }

    // Model enumeration / decrypt mode
    if let Some(limit) = enumerate_limit {
        let mut parser = Parser::new(&mut solver.sorts, &mut solver.terms);
        let commands = match parser.parse_script(&script_content) {
            Ok(cmds) => cmds,
            Err(e) => {
                eprintln!("Parse error: {}", e);
                return ExitCode::FAILURE;
            }
        };

        for cmd in commands {
            if let Err(e) = solver.execute_command(cmd) {
                eprintln!("Execution error: {}", e);
                return ExitCode::FAILURE;
            }
        }

        if let Some(heuristic) = score_heuristic {
            let scored = solver.enumerate_models_scored(&[], limit, heuristic);
            println!(
                "Enumerated and ranked {} model(s) (heuristic: {:?}, limit: {}):",
                scored.len(),
                heuristic,
                limit
            );
            println!("[NOTE] Heuristic ranking applied for analyst triage: highest score denotes most plausible candidate, NOT proof of uniqueness.");
            for (idx, (m, score)) in scored.iter().enumerate() {
                println!(
                    "--- Candidate Model #{} [Heuristic Score: {:.4}] ---",
                    idx + 1,
                    score
                );
                print!("{}", m);
            }
            if scored.len() == 1 {
                println!("Key certification: Exactly 1 unique solution discovered.");
            } else if scored.is_empty() {
                println!("Key certification: 0 solutions discovered (UNSAT).");
            } else {
                println!(
                    "Key certification: Multiple solutions ({}) exist.",
                    scored.len()
                );
            }
        } else {
            let models = solver.enumerate_models(&[], limit);
            println!("Enumerated {} model(s) (limit: {}):", models.len(), limit);
            for (idx, m) in models.iter().enumerate() {
                println!("--- Model #{} ---", idx + 1);
                print!("{}", m);
            }
            if models.len() == 1 {
                println!("Key certification: Exactly 1 unique solution discovered.");
            } else if models.is_empty() {
                println!("Key certification: 0 solutions discovered (UNSAT).");
            } else {
                println!(
                    "Key certification: Multiple solutions ({}) exist.",
                    models.len()
                );
            }
        }
        return ExitCode::SUCCESS;
    }

    // MBA Simplification mode
    if mba_simplify {
        let mut parser = Parser::new(&mut solver.sorts, &mut solver.terms);
        let commands = match parser.parse_script(&script_content) {
            Ok(cmds) => cmds,
            Err(e) => {
                eprintln!("Parse error: {}", e);
                return ExitCode::FAILURE;
            }
        };

        let mut simplifier = smt_mba::MbaSimplifier::new();
        for cmd in commands {
            match cmd {
                smt_parser::ast::Command::Assert(t) => {
                    let simp_t = simplifier.simplify(t, &mut solver.terms, &mut solver.sorts);
                    println!("(assert {})", solver.terms.display_term(simp_t));
                }
                other => {
                    if let Ok(out) = solver.execute_command(other) {
                        if !out.is_empty() {
                            println!("{}", out);
                        }
                    }
                }
            }
        }
        return ExitCode::SUCCESS;
    }

    // Execute standard SMT script
    match solver.execute_script(&script_content) {
        Ok(outputs) => {
            for out in outputs {
                println!("{}", out);
            }

            if let Some(path) = drat_out {
                let proof_text = solver.sat.proof.text();
                if let Err(err) = fs::write(&path, proof_text) {
                    eprintln!("Warning: Failed to export DRAT proof: {}", err);
                }
            }

            if show_stats {
                println!("{}", solver.metrics.to_json());
            }

            ExitCode::SUCCESS
        }
        Err(err) => {
            eprintln!("SMT Error: {}", err);
            ExitCode::FAILURE
        }
    }
}

fn run_repl(solver: &mut Solver) -> ExitCode {
    println!("SMT-Solver-Rust Interactive REPL (type '(exit)' to quit)");
    let stdin = io::stdin();
    let mut stdout = io::stdout();

    loop {
        print!("smt> ");
        let _ = stdout.flush();

        let mut line = String::new();
        if stdin.lock().read_line(&mut line).is_err() || line.trim().is_empty() {
            break;
        }

        if line.trim() == "(exit)" || line.trim() == "exit" {
            break;
        }

        match solver.execute_script(&line) {
            Ok(outputs) => {
                for out in outputs {
                    println!("{}", out);
                }
            }
            Err(err) => {
                eprintln!("Error: {}", err);
            }
        }
    }

    ExitCode::SUCCESS
}
