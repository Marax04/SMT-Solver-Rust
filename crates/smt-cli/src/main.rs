//! Command-line interface and interactive REPL for the pure Rust SMT Solver.

use smt_parser::binary::{BinaryDecoder, BinaryEncoder};
use smt_parser::parser::Parser;
use smt_solver::engine::Solver;
use smt_solver::opaque::OpaqueClassification;
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
                        "ascii" => score_heuristic = Some(smt_solver::ScoreHeuristic::AsciiPrintable),
                        "entropy" => score_heuristic = Some(smt_solver::ScoreHeuristic::Entropy),
                        "weight" => score_heuristic = Some(smt_solver::ScoreHeuristic::LowHammingWeight),
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
                println!("--- Candidate Model #{} [Heuristic Score: {:.4}] ---", idx + 1, score);
                print!("{}", m);
            }
            if scored.len() == 1 {
                println!("Key certification: Exactly 1 unique solution discovered.");
            } else if scored.is_empty() {
                println!("Key certification: 0 solutions discovered (UNSAT).");
            } else {
                println!("Key certification: Multiple solutions ({}) exist.", scored.len());
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
                println!("Key certification: Multiple solutions ({}) exist.", models.len());
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
