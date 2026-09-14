//! Lexer and Token definitions for SMT-LIB 2.6 standard.

use num_bigint::{BigInt, BigUint};
use num_rational::BigRational;
use smt_core::diagnostics::{SmtError, Span};
use std::str::FromStr;

/// SMT-LIB2 lexical tokens.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Token {
    LParen,
    RParen,
    Symbol(String),
    Keyword(String),
    Numeral(BigInt),
    Decimal(BigRational),
    HexLiteral { value: BigUint, width: u32 },
    BinaryLiteral { value: BigUint, width: u32 },
    StringLiteral(String),
}

/// Zero-copy lexical scanner for SMT-LIB2 inputs.
pub struct Lexer<'a> {
    input: &'a str,
    chars: std::iter::Peekable<std::str::CharIndices<'a>>,
    line: usize,
    col: usize,
}

impl<'a> Lexer<'a> {
    /// Creates a new lexer over the given string.
    pub fn new(input: &'a str) -> Self {
        let clean_input = input.strip_prefix('\u{feff}').unwrap_or(input);
        Self {
            input: clean_input,
            chars: clean_input.char_indices().peekable(),
            line: 1,
            col: 1,
        }
    }

    /// Current source code position span.
    pub fn span(&self) -> Span {
        Span::new(self.line, self.col)
    }

    fn advance(&mut self) -> Option<(usize, char)> {
        if let Some((idx, ch)) = self.chars.next() {
            if ch == '\n' {
                self.line += 1;
                self.col = 1;
            } else {
                self.col += 1;
            }
            Some((idx, ch))
        } else {
            None
        }
    }

    fn peek(&mut self) -> Option<char> {
        self.chars.peek().map(|&(_, ch)| ch)
    }

    /// Scans the next token in the stream.
    pub fn next_token(&mut self) -> Result<Option<(Token, Span)>, SmtError> {
        loop {
            // Skip whitespace
            while let Some(ch) = self.peek() {
                if ch.is_whitespace() {
                    self.advance();
                } else {
                    break;
                }
            }

            // Skip comments (; to end of line)
            if let Some(';') = self.peek() {
                while let Some((_, ch)) = self.advance() {
                    if ch == '\n' {
                        break;
                    }
                }
                continue;
            }

            break;
        }

        let start_span = self.span();
        let (start_idx, ch) = match self.advance() {
            Some(pair) => pair,
            None => return Ok(None),
        };

        match ch {
            '(' => Ok(Some((Token::LParen, start_span))),
            ')' => Ok(Some((Token::RParen, start_span))),
            ':' => {
                // Keyword: :symbol
                let mut end_idx = start_idx + 1;
                while let Some(next_ch) = self.peek() {
                    if is_symbol_char(next_ch) {
                        if let Some((idx, _)) = self.advance() {
                            end_idx = idx + 1;
                        }
                    } else {
                        break;
                    }
                }
                let kw = self.input[start_idx + 1..end_idx].to_string();
                Ok(Some((Token::Keyword(kw), start_span)))
            }
            '#' => {
                // Bit-vector literals #x[hex] or #b[bin]
                match self.advance() {
                    Some((_, 'x')) => {
                        let mut hex_str = String::new();
                        while let Some(next_ch) = self.peek() {
                            if next_ch.is_ascii_hexdigit() {
                                self.advance();
                                hex_str.push(next_ch);
                            } else {
                                break;
                            }
                        }
                        if hex_str.is_empty() {
                            return Err(SmtError::Parse {
                                message: "Expected hex digits after #x".to_string(),
                                span: start_span,
                            });
                        }
                        let width = (hex_str.len() * 4) as u32;
                        let value = BigUint::parse_bytes(hex_str.as_bytes(), 16).unwrap();
                        Ok(Some((Token::HexLiteral { value, width }, start_span)))
                    }
                    Some((_, 'b')) => {
                        let mut bin_str = String::new();
                        while let Some(next_ch) = self.peek() {
                            if next_ch == '0' || next_ch == '1' {
                                self.advance();
                                bin_str.push(next_ch);
                            } else {
                                break;
                            }
                        }
                        if bin_str.is_empty() {
                            return Err(SmtError::Parse {
                                message: "Expected binary digits after #b".to_string(),
                                span: start_span,
                            });
                        }
                        let width = bin_str.len() as u32;
                        let value = BigUint::parse_bytes(bin_str.as_bytes(), 2).unwrap();
                        Ok(Some((Token::BinaryLiteral { value, width }, start_span)))
                    }
                    _ => Err(SmtError::Parse {
                        message: "Invalid token starting with #".to_string(),
                        span: start_span,
                    }),
                }
            }
            '"' => {
                // String literal
                let mut s = String::new();
                while let Some((_, ch)) = self.advance() {
                    if ch == '"' {
                        return Ok(Some((Token::StringLiteral(s), start_span)));
                    }
                    s.push(ch);
                }
                Err(SmtError::Parse {
                    message: "Unterminated string literal".to_string(),
                    span: start_span,
                })
            }
            '|' => {
                // Quoted symbol |symbol with spaces|
                let mut s = String::new();
                while let Some((_, ch)) = self.advance() {
                    if ch == '|' {
                        return Ok(Some((Token::Symbol(s), start_span)));
                    }
                    s.push(ch);
                }
                Err(SmtError::Parse {
                    message: "Unterminated quoted symbol".to_string(),
                    span: start_span,
                })
            }
            _ if ch.is_ascii_digit() => {
                let mut num_str = String::new();
                num_str.push(ch);
                let mut is_decimal = false;

                while let Some(next_ch) = self.peek() {
                    if next_ch.is_ascii_digit() {
                        self.advance();
                        num_str.push(next_ch);
                    } else if next_ch == '.' && !is_decimal {
                        self.advance();
                        num_str.push(next_ch);
                        is_decimal = true;
                    } else {
                        break;
                    }
                }

                if is_decimal {
                    let parts: Vec<&str> = num_str.split('.').collect();
                    let whole: BigInt = parts[0].parse().unwrap();
                    let frac_str = parts[1];
                    let frac: BigInt = frac_str.parse().unwrap();
                    let denom = BigInt::from(10).pow(frac_str.len() as u32);
                    let val = BigRational::from_integer(whole) + BigRational::new(frac, denom);
                    Ok(Some((Token::Decimal(val), start_span)))
                } else {
                    let val = BigInt::from_str(&num_str).unwrap();
                    Ok(Some((Token::Numeral(val), start_span)))
                }
            }
            _ if is_symbol_start(ch) => {
                let mut sym = String::new();
                sym.push(ch);
                while let Some(next_ch) = self.peek() {
                    if is_symbol_char(next_ch) {
                        self.advance();
                        sym.push(next_ch);
                    } else {
                        break;
                    }
                }
                Ok(Some((Token::Symbol(sym), start_span)))
            }
            _ => Err(SmtError::Parse {
                message: format!("Unexpected character: '{}'", ch),
                span: start_span,
            }),
        }
    }
}

fn is_symbol_start(ch: char) -> bool {
    ch.is_alphabetic() || "~!@$%^&*_-+=<>.?/".contains(ch)
}

fn is_symbol_char(ch: char) -> bool {
    is_symbol_start(ch) || ch.is_ascii_digit()
}
