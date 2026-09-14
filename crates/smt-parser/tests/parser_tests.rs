use smt_core::sort::SortArena;
use smt_core::term::TermArena;
use smt_parser::ast::Command;
use smt_parser::binary::{BinaryDecoder, BinaryEncoder};
use smt_parser::parser::Parser;

#[test]
fn test_parse_simple_script() {
    let input = r#"
        (set-logic QF_BV)
        (declare-const x (_ BitVec 32))
        (declare-const y (_ BitVec 32))
        (assert (= (bvadd x y) #x0000002a))
        (check-sat)
    "#;

    let mut sorts = SortArena::new();
    let mut terms = TermArena::new(&mut sorts);
    let mut parser = Parser::new(&mut sorts, &mut terms);

    let commands = parser.parse_script(input).unwrap();
    assert_eq!(commands.len(), 5);
    assert!(matches!(commands[0], Command::SetLogic(_)));
    assert!(matches!(commands[1], Command::DeclareConst(ref name, _) if name == "x"));
    assert!(matches!(commands[2], Command::DeclareConst(ref name, _) if name == "y"));
    assert!(matches!(commands[3], Command::Assert(_)));
    assert!(matches!(commands[4], Command::CheckSat));
}

#[test]
fn test_parse_let_binding() {
    let input = r#"
        (declare-const a Bool)
        (assert (let ((b (not a))) (and a b)))
        (check-sat)
    "#;

    let mut sorts = SortArena::new();
    let mut terms = TermArena::new(&mut sorts);
    let mut parser = Parser::new(&mut sorts, &mut terms);

    let commands = parser.parse_script(input).unwrap();
    assert_eq!(commands.len(), 3);
}

#[test]
fn test_binary_roundtrip() {
    let mut sorts = SortArena::new();
    let mut terms = TermArena::new(&mut sorts);

    let cmd1 = Command::SetLogic("QF_BV".to_string());
    let cmd2 = Command::CheckSat;
    let cmd3 = Command::GetModel;
    let commands = vec![cmd1, cmd2, cmd3];

    let encoder = BinaryEncoder::new(&sorts, &terms);
    let bytes = encoder.encode_commands(&commands);

    let mut decoder = BinaryDecoder::new(&mut sorts, &mut terms);
    let decoded = decoder.decode_commands(&bytes).unwrap();

    assert_eq!(decoded.len(), 3);
    assert!(matches!(decoded[0], Command::SetLogic(_)));
    assert!(matches!(decoded[1], Command::CheckSat));
    assert!(matches!(decoded[2], Command::GetModel));
}
