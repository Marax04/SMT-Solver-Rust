//! Compact binary serialization format (smt-bin) for formulas and models.

use crate::ast::Command;
use num_bigint::{BigInt, BigUint, Sign};
use num_rational::BigRational;
use smt_core::diagnostics::{SmtError, SmtResult, Span};
use smt_core::sort::{Sort, SortArena, SortId};
use smt_core::term::{Op, TermArena, TermId};

const MAGIC: &[u8; 4] = b"SMTB";
const VERSION: u8 = 1;

/// Binary serializer for high-speed inter-process communication.
pub struct BinaryEncoder<'a> {
    pub sorts: &'a SortArena,
    pub terms: &'a TermArena,
}

impl<'a> BinaryEncoder<'a> {
    pub fn new(sorts: &'a SortArena, terms: &'a TermArena) -> Self {
        Self { sorts, terms }
    }

    /// Encodes sorts, terms, and commands to binary.
    pub fn encode_commands(&self, commands: &[Command]) -> Vec<u8> {
        let mut buf = Vec::with_capacity(8192);
        buf.extend_from_slice(MAGIC);
        buf.push(VERSION);

        // --- Section 1: Non-default Sorts (starting from index 3) ---
        let sort_len = self.sorts.len();
        encode_u32(&mut buf, (sort_len.saturating_sub(3)) as u32);
        for s in 3..sort_len {
            encode_sort(&mut buf, self.sorts.get(SortId(s as u32)));
        }

        // --- Section 2: Non-default Terms (starting from index 2) ---
        let term_len = self.terms.len();
        encode_u32(&mut buf, (term_len.saturating_sub(2)) as u32);
        for t in 2..term_len {
            let term = self.terms.get(TermId(t as u32));
            encode_u32(&mut buf, term.sort.0);
            encode_u32(&mut buf, term.args.len() as u32);
            for &arg in &term.args {
                encode_u32(&mut buf, arg.0);
            }
            encode_op(&mut buf, &term.op);
        }

        // --- Section 3: Commands ---
        encode_u32(&mut buf, commands.len() as u32);
        for cmd in commands {
            match cmd {
                Command::SetLogic(l) => {
                    buf.push(1);
                    encode_string(&mut buf, l);
                }
                Command::DeclareConst(name, sort) => {
                    buf.push(2);
                    encode_string(&mut buf, name);
                    encode_u32(&mut buf, sort.0);
                }
                Command::Assert(term) => {
                    buf.push(3);
                    encode_u32(&mut buf, term.0);
                }
                Command::CheckSat => {
                    buf.push(4);
                }
                Command::GetModel => {
                    buf.push(5);
                }
                Command::Exit => {
                    buf.push(6);
                }
                Command::DeclareFun(name, arg_sorts, ret_sort) => {
                    buf.push(7);
                    encode_string(&mut buf, name);
                    encode_u32(&mut buf, arg_sorts.len() as u32);
                    for &arg_sort in arg_sorts {
                        encode_u32(&mut buf, arg_sort.0);
                    }
                    encode_u32(&mut buf, ret_sort.0);
                }
                Command::DeclareSort(name, arity) => {
                    buf.push(8);
                    encode_string(&mut buf, name);
                    encode_u32(&mut buf, *arity);
                }
                _ => {
                    buf.push(0);
                }
            }
        }

        buf
    }
}

/// Binary deserializer for high-speed ingestion.
pub struct BinaryDecoder<'a> {
    pub sorts: &'a mut SortArena,
    pub terms: &'a mut TermArena,
}

impl<'a> BinaryDecoder<'a> {
    pub fn new(sorts: &'a mut SortArena, terms: &'a mut TermArena) -> Self {
        Self { sorts, terms }
    }

    /// Decodes a binary payload into a list of commands, reconstructing Sorts and Terms.
    pub fn decode_commands(&mut self, data: &[u8]) -> SmtResult<Vec<Command>> {
        if data.len() < 5 || &data[0..4] != MAGIC {
            return Err(SmtError::Parse {
                message: "Invalid binary SMT header".to_string(),
                span: Span::dummy(),
            });
        }

        let version = data[4];
        if version != VERSION {
            return Err(SmtError::Parse {
                message: format!("Unsupported binary SMT version: {}", version),
                span: Span::dummy(),
            });
        }

        let mut offset = 5;

        // --- Section 1: Decode Sorts ---
        let sort_count = decode_u32(data, &mut offset)? as usize;
        for _ in 0..sort_count {
            let sort = decode_sort(data, &mut offset)?;
            self.sorts.intern(sort);
        }

        // --- Section 2: Decode Terms ---
        let term_count = decode_u32(data, &mut offset)? as usize;
        for _ in 0..term_count {
            let sort_id = SortId(decode_u32(data, &mut offset)?);
            let args_len = decode_u32(data, &mut offset)? as usize;
            let mut args = Vec::with_capacity(args_len);
            for _ in 0..args_len {
                args.push(TermId(decode_u32(data, &mut offset)?));
            }
            let op = decode_op(data, &mut offset)?;
            self.terms.intern(op, args, sort_id);
        }

        // --- Section 3: Decode Commands ---
        let count = decode_u32(data, &mut offset)? as usize;
        let mut commands = Vec::with_capacity(count);

        for _ in 0..count {
            if offset >= data.len() {
                break;
            }
            let tag = data[offset];
            offset += 1;

            match tag {
                1 => {
                    let l = decode_string(data, &mut offset)?;
                    commands.push(Command::SetLogic(l));
                }
                2 => {
                    let name = decode_string(data, &mut offset)?;
                    let sort_id = SortId(decode_u32(data, &mut offset)?);
                    commands.push(Command::DeclareConst(name, sort_id));
                }
                3 => {
                    let term_id = TermId(decode_u32(data, &mut offset)?);
                    commands.push(Command::Assert(term_id));
                }
                4 => commands.push(Command::CheckSat),
                5 => commands.push(Command::GetModel),
                6 => commands.push(Command::Exit),
                7 => {
                    let name = decode_string(data, &mut offset)?;
                    let args_len = decode_u32(data, &mut offset)? as usize;
                    let mut arg_sorts = Vec::with_capacity(args_len);
                    for _ in 0..args_len {
                        arg_sorts.push(SortId(decode_u32(data, &mut offset)?));
                    }
                    let ret_sort = SortId(decode_u32(data, &mut offset)?);
                    commands.push(Command::DeclareFun(name, arg_sorts, ret_sort));
                }
                8 => {
                    let name = decode_string(data, &mut offset)?;
                    let arity = decode_u32(data, &mut offset)?;
                    commands.push(Command::DeclareSort(name, arity));
                }
                _ => {}
            }
        }

        Ok(commands)
    }
}

fn encode_sort(buf: &mut Vec<u8>, sort: &Sort) {
    match sort {
        Sort::Bool => buf.push(0),
        Sort::BitVec(w) => {
            buf.push(1);
            encode_u32(buf, *w);
        }
        Sort::Int => buf.push(2),
        Sort::Real => buf.push(3),
        Sort::Array { index, element } => {
            buf.push(4);
            encode_u32(buf, index.0);
            encode_u32(buf, element.0);
        }
        Sort::Uninterpreted(s) => {
            buf.push(5);
            encode_string(buf, s);
        }
    }
}

fn decode_sort(data: &[u8], offset: &mut usize) -> SmtResult<Sort> {
    if *offset >= data.len() {
        return Err(SmtError::Parse {
            message: "Unexpected end of binary stream in sort".to_string(),
            span: Span::dummy(),
        });
    }
    let tag = data[*offset];
    *offset += 1;
    match tag {
        0 => Ok(Sort::Bool),
        1 => {
            let w = decode_u32(data, offset)?;
            Ok(Sort::BitVec(w))
        }
        2 => Ok(Sort::Int),
        3 => Ok(Sort::Real),
        4 => {
            let index = SortId(decode_u32(data, offset)?);
            let element = SortId(decode_u32(data, offset)?);
            Ok(Sort::Array { index, element })
        }
        5 => {
            let s = decode_string(data, offset)?;
            Ok(Sort::Uninterpreted(s))
        }
        other => Err(SmtError::Parse {
            message: format!("Unknown sort tag: {}", other),
            span: Span::dummy(),
        }),
    }
}

fn encode_op(buf: &mut Vec<u8>, op: &Op) {
    match op {
        Op::True => buf.push(0),
        Op::False => buf.push(1),
        Op::Var(s) => {
            buf.push(2);
            encode_string(buf, s);
        }
        Op::Not => buf.push(3),
        Op::And => buf.push(4),
        Op::Or => buf.push(5),
        Op::Xor => buf.push(6),
        Op::Implies => buf.push(7),
        Op::Ite => buf.push(8),
        Op::Eq => buf.push(9),
        Op::Distinct => buf.push(10),
        Op::BvConst { value, width } => {
            buf.push(11);
            encode_u32(buf, *width);
            encode_biguint(buf, value);
        }
        Op::BvNot => buf.push(12),
        Op::BvAnd => buf.push(13),
        Op::BvOr => buf.push(14),
        Op::BvXor => buf.push(15),
        Op::BvAdd => buf.push(16),
        Op::BvSub => buf.push(17),
        Op::BvMul => buf.push(18),
        Op::BvUdiv => buf.push(19),
        Op::BvUrem => buf.push(20),
        Op::BvShl => buf.push(21),
        Op::BvLshr => buf.push(22),
        Op::BvAshr => buf.push(23),
        Op::BvUlt => buf.push(24),
        Op::BvUle => buf.push(25),
        Op::BvUgt => buf.push(26),
        Op::BvUge => buf.push(27),
        Op::BvSlt => buf.push(28),
        Op::BvSle => buf.push(29),
        Op::BvSgt => buf.push(30),
        Op::BvSge => buf.push(31),
        Op::BvNeg => buf.push(32),
        Op::BvConcat => buf.push(33),
        Op::BvExtract { high, low } => {
            buf.push(34);
            encode_u32(buf, *high);
            encode_u32(buf, *low);
        }
        Op::IntConst(i) => {
            buf.push(35);
            encode_bigint(buf, i);
        }
        Op::RealConst(r) => {
            buf.push(36);
            encode_bigint(buf, r.numer());
            encode_bigint(buf, r.denom());
        }
        Op::Add => buf.push(37),
        Op::Sub => buf.push(38),
        Op::Mul => buf.push(39),
        Op::Div => buf.push(40),
        Op::Mod => buf.push(41),
        Op::Lt => buf.push(42),
        Op::Le => buf.push(43),
        Op::Gt => buf.push(44),
        Op::Ge => buf.push(45),
        Op::Select => buf.push(46),
        Op::Store => buf.push(47),
        Op::Apply(s) => {
            buf.push(48);
            encode_string(buf, s);
        }
        Op::BvSdiv => buf.push(49),
        Op::BvSrem => buf.push(50),
        Op::BvSmod => buf.push(51),
        Op::BvNand => buf.push(52),
        Op::BvNor => buf.push(53),
        Op::BvXnor => buf.push(54),
        Op::BvRotateLeft(n) => {
            buf.push(55);
            encode_u32(buf, *n);
        }
        Op::BvRotateRight(n) => {
            buf.push(56);
            encode_u32(buf, *n);
        }
        Op::BvSignExtend(n) => {
            buf.push(57);
            encode_u32(buf, *n);
        }
        Op::BvZeroExtend(n) => {
            buf.push(58);
            encode_u32(buf, *n);
        }
        Op::BvRepeat(n) => {
            buf.push(59);
            encode_u32(buf, *n);
        }
        Op::Rem => buf.push(60),
        Op::Neg => buf.push(61),
        Op::ToReal => buf.push(62),
        Op::ToInt => buf.push(63),
        Op::IsInt => buf.push(64),
        Op::ConstArray(sort_id) => {
            buf.push(65);
            encode_u32(buf, sort_id.0);
        }
    }
}

fn decode_op(data: &[u8], offset: &mut usize) -> SmtResult<Op> {
    if *offset >= data.len() {
        return Err(SmtError::Parse {
            message: "Unexpected end of binary stream in op".to_string(),
            span: Span::dummy(),
        });
    }
    let tag = data[*offset];
    *offset += 1;
    match tag {
        0 => Ok(Op::True),
        1 => Ok(Op::False),
        2 => {
            let s = decode_string(data, offset)?;
            Ok(Op::Var(s))
        }
        3 => Ok(Op::Not),
        4 => Ok(Op::And),
        5 => Ok(Op::Or),
        6 => Ok(Op::Xor),
        7 => Ok(Op::Implies),
        8 => Ok(Op::Ite),
        9 => Ok(Op::Eq),
        10 => Ok(Op::Distinct),
        11 => {
            let width = decode_u32(data, offset)?;
            let value = decode_biguint(data, offset)?;
            Ok(Op::BvConst { value, width })
        }
        12 => Ok(Op::BvNot),
        13 => Ok(Op::BvAnd),
        14 => Ok(Op::BvOr),
        15 => Ok(Op::BvXor),
        16 => Ok(Op::BvAdd),
        17 => Ok(Op::BvSub),
        18 => Ok(Op::BvMul),
        19 => Ok(Op::BvUdiv),
        20 => Ok(Op::BvUrem),
        21 => Ok(Op::BvShl),
        22 => Ok(Op::BvLshr),
        23 => Ok(Op::BvAshr),
        24 => Ok(Op::BvUlt),
        25 => Ok(Op::BvUle),
        26 => Ok(Op::BvUgt),
        27 => Ok(Op::BvUge),
        28 => Ok(Op::BvSlt),
        29 => Ok(Op::BvSle),
        30 => Ok(Op::BvSgt),
        31 => Ok(Op::BvSge),
        32 => Ok(Op::BvNeg),
        33 => Ok(Op::BvConcat),
        34 => {
            let high = decode_u32(data, offset)?;
            let low = decode_u32(data, offset)?;
            Ok(Op::BvExtract { high, low })
        }
        35 => {
            let i = decode_bigint(data, offset)?;
            Ok(Op::IntConst(i))
        }
        36 => {
            let numer = decode_bigint(data, offset)?;
            let denom = decode_bigint(data, offset)?;
            Ok(Op::RealConst(BigRational::new(numer, denom)))
        }
        37 => Ok(Op::Add),
        38 => Ok(Op::Sub),
        39 => Ok(Op::Mul),
        40 => Ok(Op::Div),
        41 => Ok(Op::Mod),
        42 => Ok(Op::Lt),
        43 => Ok(Op::Le),
        44 => Ok(Op::Gt),
        45 => Ok(Op::Ge),
        46 => Ok(Op::Select),
        47 => Ok(Op::Store),
        48 => {
            let s = decode_string(data, offset)?;
            Ok(Op::Apply(s))
        }
        49 => Ok(Op::BvSdiv),
        50 => Ok(Op::BvSrem),
        51 => Ok(Op::BvSmod),
        52 => Ok(Op::BvNand),
        53 => Ok(Op::BvNor),
        54 => Ok(Op::BvXnor),
        55 => {
            let n = decode_u32(data, offset)?;
            Ok(Op::BvRotateLeft(n))
        }
        56 => {
            let n = decode_u32(data, offset)?;
            Ok(Op::BvRotateRight(n))
        }
        57 => {
            let n = decode_u32(data, offset)?;
            Ok(Op::BvSignExtend(n))
        }
        58 => {
            let n = decode_u32(data, offset)?;
            Ok(Op::BvZeroExtend(n))
        }
        59 => {
            let n = decode_u32(data, offset)?;
            Ok(Op::BvRepeat(n))
        }
        60 => Ok(Op::Rem),
        61 => Ok(Op::Neg),
        62 => Ok(Op::ToReal),
        63 => Ok(Op::ToInt),
        64 => Ok(Op::IsInt),
        65 => {
            let id = decode_u32(data, offset)?;
            Ok(Op::ConstArray(SortId(id)))
        }
        other => Err(SmtError::Parse {
            message: format!("Unknown op tag: {}", other),
            span: Span::dummy(),
        }),
    }
}

fn encode_biguint(buf: &mut Vec<u8>, val: &BigUint) {
    let bytes = val.to_bytes_le();
    encode_u32(buf, bytes.len() as u32);
    buf.extend_from_slice(&bytes);
}

fn decode_biguint(data: &[u8], offset: &mut usize) -> SmtResult<BigUint> {
    let len = decode_u32(data, offset)? as usize;
    if *offset + len > data.len() {
        return Err(SmtError::Parse {
            message: "Unexpected end of binary stream in BigUint".to_string(),
            span: Span::dummy(),
        });
    }
    let val = BigUint::from_bytes_le(&data[*offset..*offset + len]);
    *offset += len;
    Ok(val)
}

fn encode_bigint(buf: &mut Vec<u8>, val: &BigInt) {
    let (sign, bytes) = val.to_bytes_le();
    let sign_byte = match sign {
        Sign::Minus => 0,
        Sign::NoSign => 1,
        Sign::Plus => 2,
    };
    buf.push(sign_byte);
    encode_u32(buf, bytes.len() as u32);
    buf.extend_from_slice(&bytes);
}

fn decode_bigint(data: &[u8], offset: &mut usize) -> SmtResult<BigInt> {
    if *offset >= data.len() {
        return Err(SmtError::Parse {
            message: "Unexpected end of binary stream in BigInt sign".to_string(),
            span: Span::dummy(),
        });
    }
    let sign_byte = data[*offset];
    *offset += 1;
    let sign = match sign_byte {
        0 => Sign::Minus,
        1 => Sign::NoSign,
        _ => Sign::Plus,
    };
    let len = decode_u32(data, offset)? as usize;
    if *offset + len > data.len() {
        return Err(SmtError::Parse {
            message: "Unexpected end of binary stream in BigInt bytes".to_string(),
            span: Span::dummy(),
        });
    }
    let i = BigInt::from_bytes_le(sign, &data[*offset..*offset + len]);
    *offset += len;
    Ok(i)
}

fn encode_u32(buf: &mut Vec<u8>, val: u32) {
    buf.extend_from_slice(&val.to_le_bytes());
}

fn decode_u32(data: &[u8], offset: &mut usize) -> SmtResult<u32> {
    if *offset + 4 > data.len() {
        return Err(SmtError::Parse {
            message: "Unexpected end of binary stream".to_string(),
            span: Span::dummy(),
        });
    }
    let bytes: [u8; 4] = data[*offset..*offset + 4].try_into().unwrap();
    *offset += 4;
    Ok(u32::from_le_bytes(bytes))
}

fn encode_string(buf: &mut Vec<u8>, s: &str) {
    encode_u32(buf, s.len() as u32);
    buf.extend_from_slice(s.as_bytes());
}

fn decode_string(data: &[u8], offset: &mut usize) -> SmtResult<String> {
    let len = decode_u32(data, offset)? as usize;
    if *offset + len > data.len() {
        return Err(SmtError::Parse {
            message: "Unexpected end of binary stream in string".to_string(),
            span: Span::dummy(),
        });
    }
    let s = String::from_utf8_lossy(&data[*offset..*offset + len]).to_string();
    *offset += len;
    Ok(s)
}
