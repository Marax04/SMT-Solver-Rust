//! Glucose-style dynamic LBD restarts with Luby fallback.

/// Restart heuristic manager.
#[derive(Debug, Clone)]
pub struct RestartStrategy {
    /// Fast moving average of learned clause LBD.
    fast_lbd: f64,
    /// Slow moving average of learned clause LBD.
    slow_lbd: f64,
    /// Conflicts elapsed since last restart.
    conflicts_since_restart: usize,
    /// Minimum conflict threshold before triggering dynamic restart.
    min_conflicts: usize,
    /// Total number of restarts performed.
    pub restart_count: usize,
    /// Luby restart sequence counter.
    luby_index: usize,
    /// Luby base unit.
    luby_unit: usize,
}

impl Default for RestartStrategy {
    fn default() -> Self {
        Self::new()
    }
}

impl RestartStrategy {
    /// Creates a new restart controller.
    pub fn new() -> Self {
        Self {
            fast_lbd: 0.0,
            slow_lbd: 0.0,
            conflicts_since_restart: 0,
            min_conflicts: 50,
            restart_count: 0,
            luby_index: 1,
            luby_unit: 100,
        }
    }

    /// Registers a learned clause LBD and returns true if a restart is recommended.
    pub fn record_conflict(&mut self, lbd: u32) -> bool {
        let lbd_val = lbd as f64;
        if self.fast_lbd == 0.0 {
            self.fast_lbd = lbd_val;
            self.slow_lbd = lbd_val;
        } else {
            // Fast alpha = 0.03
            self.fast_lbd += 0.03 * (lbd_val - self.fast_lbd);
            // Slow beta = 0.0003
            self.slow_lbd += 0.0003 * (lbd_val - self.slow_lbd);
        }

        self.conflicts_since_restart += 1;

        // Glucose restart condition: recent clauses have notably higher LBD than global average
        if self.conflicts_since_restart >= self.min_conflicts && self.fast_lbd > 1.25 * self.slow_lbd {
            self.on_restart();
            return true;
        }

        // Luby threshold fallback
        let luby_threshold = luby(self.luby_index) * self.luby_unit;
        if self.conflicts_since_restart >= luby_threshold {
            self.luby_index += 1;
            self.on_restart();
            return true;
        }

        false
    }

    fn on_restart(&mut self) {
        self.conflicts_since_restart = 0;
        self.restart_count += 1;
    }
}

/// Computes the k-th term in the Luby sequence: 1, 1, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 2, 4, 8...
fn luby(mut i: usize) -> usize {
    let mut size = 1;
    while size <= i {
        size = 2 * size + 1;
    }
    while size - 1 != i {
        size = (size - 1) / 2;
        if i >= size {
            i -= size;
        }
    }
    (size + 1) / 2
}
