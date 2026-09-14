//! S-expression tree structure and parser.

use crate::lexer::{Lexer, Token};
use smt_core::diagnostics::{SmtError, Span};

/// An S-Expression node.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SExpr {
    Atom(Token, Span),
    List(Vec<SExpr>, Span),
}

impl SExpr {
    /// Returns the source span of the s-expression.
    pub fn span(&self) -> Span {
        match self {
            Self::Atom(_, s) => *s,
            Self::List(_, s) => *s,
        }
    }

    /// Helper to extract string symbol if this is a symbol atom.
    pub fn as_symbol(&self) -> Option<&str> {
        match self {
            Self::Atom(Token::Symbol(s), _) => Some(s.as_str()),
            _ => None,
        }
    }

    /// Helper to extract list slice if this is a list.
    pub fn as_list(&self) -> Option<&[SExpr]> {
        match self {
            Self::List(l, _) => Some(l.as_slice()),
            _ => None,
        }
    }
}

pub const MAX_SEXPR_DEPTH: usize = 1024;

/// Parses an SMT-LIB string into a sequence of S-Expressions.
pub fn parse_sexprs(input: &str) -> Result<Vec<SExpr>, SmtError> {
    let mut lexer = Lexer::new(input);
    let mut root_exprs = Vec::new();
    let mut stack: Vec<(Vec<SExpr>, Span)> = Vec::new();

    while let Some((token, span)) = lexer.next_token()? {
        match token {
            Token::LParen => {
                if stack.len() >= MAX_SEXPR_DEPTH {
                    return Err(SmtError::Parse {
                        message: format!("Expression nesting depth exceeded limit ({})", MAX_SEXPR_DEPTH),
                        span,
                    });
                }
                stack.push((Vec::new(), span));
            }
            Token::RParen => {
                if let Some((elements, start_span)) = stack.pop() {
                    let list_node = SExpr::List(elements, start_span);
                    if let Some((parent_list, _)) = stack.last_mut() {
                        parent_list.push(list_node);
                    } else {
                        root_exprs.push(list_node);
                    }
                } else {
                    return Err(SmtError::Parse {
                        message: "Unexpected closing parenthesis ')'".to_string(),
                        span,
                    });
                }
            }
            other_atom => {
                let atom_node = SExpr::Atom(other_atom, span);
                if let Some((current_list, _)) = stack.last_mut() {
                    current_list.push(atom_node);
                } else {
                    root_exprs.push(atom_node);
                }
            }
        }
    }

    if let Some((_, unclosed_span)) = stack.pop() {
        return Err(SmtError::Parse {
            message: "Unclosed parenthesis '('".to_string(),
            span: unclosed_span,
        });
    }

    Ok(root_exprs)
}
