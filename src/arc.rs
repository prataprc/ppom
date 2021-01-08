//! Module implement fully-persistent ordered-map, slower but thread safe.

use std::sync::Arc as Ref;

#[path = "./ppom.rs"]
mod ppom;

pub use self::ppom::OMap;

impl<K, V> OMap<K, V> {
    /// Return whether this instance is thread-safe.
    pub fn is_thread_safe(&self) -> bool {
        true
    }
}

#[cfg(test)]
#[path = "arc_test.rs"]
mod arc_test;
