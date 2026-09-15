//! Sorts and Sort intern arena representation.

use std::collections::HashMap;
use std::fmt;

/// Unique identifier referencing an interned Sort in a `SortArena`.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct SortId(pub u32);

impl fmt::Display for SortId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "sort#{}", self.0)
    }
}

/// SMT-LIB supported sorts.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Sort {
    /// Boolean logic sort.
    Bool,
    /// Bit-vector sort with a strictly positive bit-width.
    BitVec(u32),
    /// Unbounded mathematical integers.
    Int,
    /// Real numbers (exact rationals).
    Real,
    /// Extensional arrays mapping index sort to element sort.
    Array { index: SortId, element: SortId },
    /// Custom uninterpreted sort symbol.
    Uninterpreted(String),
}

impl fmt::Display for Sort {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Bool => write!(f, "Bool"),
            Self::BitVec(w) => write!(f, "(_ BitVec {})", w),
            Self::Int => write!(f, "Int"),
            Self::Real => write!(f, "Real"),
            Self::Array { index, element } => write!(f, "(Array {} {})", index, element),
            Self::Uninterpreted(s) => write!(f, "{}", s),
        }
    }
}

/// Hash-consing storage arena for deduplicated Sorts.
#[derive(Debug, Clone)]
pub struct SortArena {
    sorts: Vec<Sort>,
    lookup: HashMap<Sort, SortId>,
    pub bool_sort: SortId,
    pub int_sort: SortId,
    pub real_sort: SortId,
}

impl Default for SortArena {
    fn default() -> Self {
        Self::new()
    }
}

/// Maximum bit-vector width supported to prevent memory DoS attacks.
pub const MAX_BV_WIDTH: u32 = 65536;

impl SortArena {
    /// Creates a new arena pre-populated with standard primitive sorts.
    ///
    /// # Example
    /// ```rust
    /// use smt_core::sort::{Sort, SortArena};
    /// let mut arena = SortArena::new();
    /// let bv32 = arena.bv(32);
    /// assert_eq!(arena.get(bv32), &Sort::BitVec(32));
    /// ```
    pub fn new() -> Self {
        let mut arena = Self {
            sorts: Vec::with_capacity(32),
            lookup: HashMap::with_capacity(32),
            bool_sort: SortId(0),
            int_sort: SortId(0),
            real_sort: SortId(0),
        };
        arena.bool_sort = arena.intern(Sort::Bool);
        arena.int_sort = arena.intern(Sort::Int);
        arena.real_sort = arena.intern(Sort::Real);
        arena
    }

    /// Interns a Sort and returns its stable SortId.
    pub fn intern(&mut self, sort: Sort) -> SortId {
        if let Some(&id) = self.lookup.get(&sort) {
            return id;
        }
        let id = SortId(self.sorts.len() as u32);
        self.sorts.push(sort.clone());
        self.lookup.insert(sort, id);
        id
    }

    /// Interns a bitvector sort with the given width, capped at `MAX_BV_WIDTH`.
    pub fn bv(&mut self, width: u32) -> SortId {
        assert!(
            width > 0 && width <= MAX_BV_WIDTH,
            "BitVector width must be in 1..=65536"
        );
        self.intern(Sort::BitVec(width))
    }

    /// Interns an array sort with index and element sorts.
    pub fn array(&mut self, index: SortId, element: SortId) -> SortId {
        self.intern(Sort::Array { index, element })
    }

    /// Interns an uninterpreted sort.
    pub fn uninterpreted(&mut self, name: impl Into<String>) -> SortId {
        self.intern(Sort::Uninterpreted(name.into()))
    }

    /// Retrieves a reference to the Sort associated with a SortId.
    pub fn get(&self, id: SortId) -> &Sort {
        &self.sorts[id.0 as usize]
    }

    /// Returns the number of allocated sorts.
    pub fn len(&self) -> usize {
        self.sorts.len()
    }

    /// Returns true if no sorts have been allocated.
    pub fn is_empty(&self) -> bool {
        self.sorts.is_empty()
    }

    /// Formats a sort recursively by resolving internal SortIds to human-readable strings.
    pub fn display_sort(&self, id: SortId) -> String {
        match self.get(id) {
            Sort::Bool => "Bool".to_string(),
            Sort::BitVec(w) => format!("(_ BitVec {})", w),
            Sort::Int => "Int".to_string(),
            Sort::Real => "Real".to_string(),
            Sort::Array { index, element } => {
                format!(
                    "(Array {} {})",
                    self.display_sort(*index),
                    self.display_sort(*element)
                )
            }
            Sort::Uninterpreted(s) => s.clone(),
        }
    }
}
