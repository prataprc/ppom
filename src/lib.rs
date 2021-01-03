//! Package implement Persistent Ordered Map.
//!
//! There are two types implementing ordered-map, [OMap] and [Mdb], each one
//! of them tuned for specific use-case. Underneath, both of them are
//! implemented using [left-leaning-red-black][wiki-llrb].
//!
//! Simple ordered-map for single threaded use case
//! -----------------------------------------------
//!
//! - Each entry in OMap instance correspond to a {Key, Value} pair.
//! - Parametrised over `key-type` and `value-type`.
//! - CRUD operations, via set(), get(), remove() api.
//! - Full table scan, to iterate over all entries.
//! - Range scan, to iterate between a ``low`` and ``high``.
//! - Reverse iteration.
//! - Uses ownership model and borrow semantics to ensure safety.
//! - No Durability guarantee.
//! - Not thread safe.
//!
//! Constructing a new [OMap] instance and CRUD operations:
//!
//! ```
//! use ppom::OMap;
//!
//! let mut index: OMap<String,String> = OMap::new();
//! assert_eq!(index.len(), 0);
//! assert_eq!(index.is_empty(), true);
//!
//! index.set("key1".to_string(), "value1".to_string());
//! index.set("key2".to_string(), "value2".to_string());
//!
//! let n = index.len();
//! assert_eq!(n, 2);
//!
//! let value = index.get("key1").unwrap();
//! assert_eq!(value, "value1".to_string());
//! let value = index.get("key2").unwrap();
//! assert_eq!(value, "value2".to_string());
//!
//! let old_value = index.remove("key1").unwrap();
//! assert_eq!(old_value, "value1".to_string());
//! ```
//!
//! [wiki-llrb]: https://en.wikipedia.org/wiki/Left-leaning_red-black_tree

use std::{error, fmt, result};

// Short form to compose Error values.
//
// Here are few possible ways:
//
// ```ignore
// use crate::Error;
// err_at!(ParseError, msg: format!("bad argument"));
// ```
//
// ```ignore
// use crate::Error;
// err_at!(ParseError, std::io::read(buf));
// ```
//
// ```ignore
// use crate::Error;
// err_at!(ParseError, std::fs::read(file_path), format!("read failed"));
// ```
//
macro_rules! err_at {
    ($v:ident, msg: $($arg:expr),+) => {{
        let prefix = format!("{}:{}", file!(), line!());
        Err(Error::$v(prefix, format!($($arg),+)))
    }};
    ($v:ident, $e:expr) => {{
        match $e {
            Ok(val) => Ok(val),
            Err(err) => {
                let prefix = format!("{}:{}", file!(), line!());
                Err(Error::$v(prefix, format!("{}", err)))
            }
        }
    }};
    ($v:ident, $e:expr, $($arg:expr),+) => {{
        match $e {
            Ok(val) => Ok(val),
            Err(err) => {
                let prefix = format!("{}:{}", file!(), line!());
                let msg = format!($($arg),+);
                Err(Error::$v(prefix, format!("{} {}", err, msg)))
            }
        }
    }};
}

mod mdb;
mod node;
mod omap;
mod op;

pub use mdb::Mdb;
pub use omap::OMap;
pub use op::Write;

/// Error variants that are returned by this package's API.
///
/// Each variant carries a prefix, typically identifying the
/// error location.
pub enum Error {
    Fatal(String, String),
    KeyNotFound(String, String),
    InvalidCAS(String, String),
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter) -> result::Result<(), fmt::Error> {
        use Error::*;

        match self {
            Fatal(p, msg) => write!(f, "{} Fatal: {}", p, msg),
            KeyNotFound(p, msg) => write!(f, "{} KeyNotFound: {}", p, msg),
            InvalidCAS(p, msg) => write!(f, "{} InvalidCAS: {}", p, msg),
        }
    }
}

impl fmt::Debug for Error {
    fn fmt(&self, f: &mut fmt::Formatter) -> result::Result<(), fmt::Error> {
        write!(f, "{}", self)
    }
}

impl error::Error for Error {}

/// Type alias for Result return type, used by this package.
pub type Result<T> = result::Result<T, Error>;
