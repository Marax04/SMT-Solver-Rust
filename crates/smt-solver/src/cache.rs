//! Persistent, disk-backed cross-session equivalence and satisfiability cache.
//!
//! Accelerates iterative binary analysis across sessions by hashing symbolic expressions
//! and caching SMT satisfiability results, extracted models, and simplified MBA normal forms.

use std::collections::HashMap;
use std::fs;
use std::path::{Path, PathBuf};

/// Cached entry recording solver outcome for a specific SMT formula or AST term.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CachedFormulaResult {
    pub formula_sha256: String,
    pub is_sat: bool,
    pub model_str: Option<String>,
    pub simplified_term: Option<String>,
}

/// Cross-session persistent cache.
pub struct PersistentCache {
    cache_path: Option<PathBuf>,
    entries: HashMap<String, CachedFormulaResult>,
}

impl PersistentCache {
    /// Creates an in-memory cache without disk persistence.
    ///
    /// # Example
    /// ```rust
    /// use smt_solver::cache::PersistentCache;
    ///
    /// let mut cache = PersistentCache::new_in_memory();
    /// cache.insert("abc123hash".to_string(), true, Some("x".to_string()));
    /// let entry = cache.get("abc123hash").expect("Must be in cache");
    /// assert!(entry.is_sat);
    /// assert_eq!(entry.simplified_term.as_deref(), Some("x"));
    /// ```
    pub fn new_in_memory() -> Self {
        Self {
            cache_path: None,
            entries: HashMap::new(),
        }
    }

    /// Initializes a disk-backed persistent cache at the given filesystem path.
    pub fn open<P: AsRef<Path>>(path: P) -> Self {
        let p = path.as_ref().to_path_buf();
        let mut entries = HashMap::new();

        if p.exists() {
            if let Ok(content) = fs::read_to_string(&p) {
                // Parse simple line-based format: sha256|is_sat|simplified_term
                for line in content.lines() {
                    let parts: Vec<&str> = line.split('|').collect();
                    if parts.len() >= 2 {
                        let hash = parts[0].to_string();
                        let is_sat = parts[1] == "1";
                        let simplified_term = if parts.len() >= 3 && !parts[2].is_empty() {
                            Some(parts[2].to_string())
                        } else {
                            None
                        };
                        entries.insert(
                            hash.clone(),
                            CachedFormulaResult {
                                formula_sha256: hash,
                                is_sat,
                                model_str: None,
                                simplified_term,
                            },
                        );
                    }
                }
            }
        }

        Self {
            cache_path: Some(p),
            entries,
        }
    }

    /// Looks up a cached formula result by SHA-256 hash.
    pub fn get(&self, sha256: &str) -> Option<&CachedFormulaResult> {
        self.entries.get(sha256)
    }

    /// Inserts a result into the cache and persists to disk if configured.
    pub fn insert(&mut self, sha256: String, is_sat: bool, simplified: Option<String>) {
        let entry = CachedFormulaResult {
            formula_sha256: sha256.clone(),
            is_sat,
            model_str: None,
            simplified_term: simplified,
        };
        self.entries.insert(sha256, entry);

        if let Some(ref path) = self.cache_path {
            self.flush_to_disk(path);
        }
    }

    /// Returns the number of cached formula entries.
    pub fn len(&self) -> usize {
        self.entries.len()
    }

    /// Checks if the cache is empty.
    pub fn is_empty(&self) -> bool {
        self.entries.is_empty()
    }

    fn flush_to_disk(&self, path: &Path) {
        let mut content = String::new();
        for (k, v) in &self.entries {
            let sat_digit = if v.is_sat { "1" } else { "0" };
            let sim = v.simplified_term.as_deref().unwrap_or("");
            content.push_str(&format!("{}|{}|{}\n", k, sat_digit, sim));
        }
        let _ = fs::write(path, content);
    }
}
