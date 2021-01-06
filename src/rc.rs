//! Module implement fully-persistent ordered-map, faster but not thread safe.

use std::rc::Rc as Ref;

#[path = "./ppom.rs"]
mod ppom;

pub use self::ppom::OMap;

impl<K, V> OMap<K, V> {
    /// Return whether this instance is thread-safe.
    pub fn is_thread_safe(&self) -> bool {
        false
    }
}
