//! Model construction and concrete value inspection.

use smt_core::value::Value;
use std::collections::BTreeMap;
use std::fmt;

/// Concrete valuation mapping variable symbols to evaluated Values.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct Model {
    values: BTreeMap<String, Value>,
}

impl Model {
    /// Creates a new empty model.
    pub fn new() -> Self {
        Self {
            values: BTreeMap::new(),
        }
    }

    /// Inserts a variable valuation.
    pub fn insert(&mut self, name: impl Into<String>, val: Value) {
        self.values.insert(name.into(), val);
    }

    /// Evaluates a variable symbol.
    pub fn get(&self, name: &str) -> Option<&Value> {
        self.values.get(name)
    }

    /// Iterates over all variable valuations.
    pub fn iter(&self) -> impl Iterator<Item = (&String, &Value)> {
        self.values.iter()
    }

    /// Iterates over all variable names in the model.
    pub fn keys(&self) -> impl Iterator<Item = &String> {
        self.values.keys()
    }
}

impl fmt::Display for Model {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        writeln!(f, "(model")?;
        for (name, val) in &self.values {
            match val {
                Value::Bool(b) => {
                    writeln!(f, "  (define-fun {} () Bool {})", name, b)?;
                }
                Value::BitVec { value, width } => {
                    let hex_len = ((width + 3) / 4) as usize;
                    writeln!(
                        f,
                        "  (define-fun {} () (_ BitVec {}) #x{:0>width$x})",
                        name, width, value, width = hex_len
                    )?;
                }
                Value::Int(i) => {
                    if i < &0.into() {
                        writeln!(f, "  (define-fun {} () Int (- {}))", name, -i)?;
                    } else {
                        writeln!(f, "  (define-fun {} () Int {})", name, i)?;
                    }
                }
                Value::Real(r) => {
                    if r.is_integer() {
                        writeln!(f, "  (define-fun {} () Real {}.0)", name, r.to_integer())?;
                    } else {
                        writeln!(f, "  (define-fun {} () Real (/ {} {}))", name, r.numer(), r.denom())?;
                    }
                }
                _ => {
                    writeln!(f, "  (define-fun {} () _ {})", name, val)?;
                }
            }
        }
        write!(f, ")")
    }
}
