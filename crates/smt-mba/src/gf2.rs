//! Linear algebra over GF(2) and polynomial-time linear MBA decomposition (SiMBA/GAMBA style).
//!
//! Replaces exponential truth tables by setting up and solving linear systems
//! over finite fields, scaling gracefully to 5, 8, or more variables.

/// Dense matrix over the Galois Field GF(2) with row-major bit packing.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Gf2Matrix {
    pub rows: usize,
    pub cols: usize,
    /// Bit-packed rows: each row is stored as `(cols + 63) / 64` words.
    data: Vec<u64>,
    words_per_row: usize,
}

impl Gf2Matrix {
    /// Creates a new zero-initialized GF(2) matrix.
    pub fn new(rows: usize, cols: usize) -> Self {
        let words_per_row = cols.div_ceil(64);
        Self {
            rows,
            cols,
            data: vec![0; rows * words_per_row],
            words_per_row,
        }
    }

    /// Sets the bit at `(row, col)`.
    pub fn set(&mut self, row: usize, col: usize, val: bool) {
        assert!(row < self.rows && col < self.cols);
        let word_idx = row * self.words_per_row + (col / 64);
        let bit_mask = 1u64 << (col % 64);
        if val {
            self.data[word_idx] |= bit_mask;
        } else {
            self.data[word_idx] &= !bit_mask;
        }
    }

    /// Gets the bit at `(row, col)`.
    pub fn get(&self, row: usize, col: usize) -> bool {
        assert!(row < self.rows && col < self.cols);
        let word_idx = row * self.words_per_row + (col / 64);
        (self.data[word_idx] >> (col % 64)) & 1 == 1
    }

    /// Adds (XORs) `source_row` into `target_row`.
    pub fn add_row(&mut self, target_row: usize, source_row: usize) {
        let target_start = target_row * self.words_per_row;
        let source_start = source_row * self.words_per_row;
        for i in 0..self.words_per_row {
            self.data[target_start + i] ^= self.data[source_start + i];
        }
    }

    /// Performs Gaussian elimination to compute Reduced Row Echelon Form (RREF).
    /// Returns the indices of the pivot columns.
    pub fn rref(&mut self) -> Vec<usize> {
        let mut pivot_row = 0;
        let mut pivot_cols = Vec::new();

        for col in 0..self.cols {
            if pivot_row >= self.rows {
                break;
            }

            // Find pivot row with bit set in this column
            let mut found_row = None;
            for r in pivot_row..self.rows {
                if self.get(r, col) {
                    found_row = Some(r);
                    break;
                }
            }

            if let Some(r) = found_row {
                if r != pivot_row {
                    // Swap rows
                    for w in 0..self.words_per_row {
                        let idx1 = pivot_row * self.words_per_row + w;
                        let idx2 = r * self.words_per_row + w;
                        self.data.swap(idx1, idx2);
                    }
                }

                // Eliminate this column from all other rows
                for r in 0..self.rows {
                    if r != pivot_row && self.get(r, col) {
                        self.add_row(r, pivot_row);
                    }
                }

                pivot_cols.push(col);
                pivot_row += 1;
            }
        }

        pivot_cols
    }

    /// Solves the linear system `A * x = b` over GF(2).
    /// Returns a solution vector `x` if consistent.
    pub fn solve_system(a: &Gf2Matrix, b: &[bool]) -> Option<Vec<bool>> {
        assert_eq!(a.rows, b.len());
        // Augmented matrix [A | b]
        let mut aug = Gf2Matrix::new(a.rows, a.cols + 1);
        for (r, &b_val) in b.iter().enumerate().take(a.rows) {
            for c in 0..a.cols {
                aug.set(r, c, a.get(r, c));
            }
            aug.set(r, a.cols, b_val);
        }

        aug.rref();

        // Check for inconsistency: row with all zeros in A and 1 in b
        for r in 0..aug.rows {
            let mut all_zero = true;
            for c in 0..a.cols {
                if aug.get(r, c) {
                    all_zero = false;
                    break;
                }
            }
            if all_zero && aug.get(r, a.cols) {
                return None; // Inconsistent system
            }
        }

        // Back-substitute / read off solution
        let mut sol = vec![false; a.cols];
        for r in 0..aug.rows {
            for (c, item) in sol.iter_mut().enumerate().take(a.cols) {
                if aug.get(r, c) {
                    *item = aug.get(r, a.cols);
                    break;
                }
            }
        }

        Some(sol)
    }
}
