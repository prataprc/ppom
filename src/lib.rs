//! Package implement Persistent Ordered Map.
//!
//! Quoting from [Wikipedia][pds]:
//!
//! > A data structure is *partially persistent* if all versions can be
//! > accessed but only the newest version can be modified. The data
//! > structure is *fully persistent* if every version can be both accessed
//! > and modified. If there is also a meld or merge operation that can
//! > create a new version from two previous versions, the data structure is
//! > called *confluently persistent*. Structures that are not persistent are
//! > called *ephemeral* data structures.
//!
//! Following types implement an ordered-map for specific use cases:
//!
//! * [OMap] implement *ephemeral* ordered-map, that is meant for best case
//!   single-threaded performance.
//! * [rc::OMap] implement *fully persistent* ordered-map that allows
//!   shared-ownership, but not thread-safe.
//! * [arc::OMap] implement *fully persistent* ordered-map that allows
//!   shared-ownership and thread-safe.
//! * [Mdb] implements *partially persistent* ordered-map most useful for
//!   database applications.
//!
//! All the above types use [Left-Leaning-Red-Black][wiki-llrb] tree underneath.
//!
//! Ephemeral ordered-map
//! ---------------------
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
//! Ownership and Cloning
//! ---------------------
//!
//! Cloning `arc::OMap` and `rc::OMap` is cheap, it creates a shared ownership
//! of the underlying tree. This is great for applications requiring
//! shared-ownership, but at the cost of copy-on-write for every mutation, like
//! set and remove operations.
//!
//! Thread Safety
//! -------------
//!
//! `arc::OMap` is thread safe through `Arc`. To trade-off thread-safety for
//! performance use `rc::OMap` type, which is same as `arc::OMap` type except
//! for using `std::rc::Rc` instead of `std::sync::Arc` for shared ownership.
//! That is, `Send` and `Sync` traits are not available for `rc::OMap` type
//! while it is available for `arc::OMap` type.
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
//! assert_eq!(index.len(), 2);
//! assert_eq!(index.get("key1").unwrap(), "value1".to_string());
//! assert_eq!(index.remove("key1").unwrap(), "value1".to_string());
//! ```
//!
//! Fully persistent ordered-map
//! ----------------------------
//!
//! Supports all the features as that of ephemeral OMap, with slight difference
//! in call pattern:
//!
//! ```
//! use ppom::rc::OMap;
//!
//! let mut index: OMap<String,String> = OMap::new();
//! assert_eq!(index.len(), 0);
//! assert_eq!(index.is_empty(), true);
//!
//! index = index.set("key1".to_string(), "value1".to_string());
//! index = index.set("key2".to_string(), "value2".to_string());
//!
//! assert_eq!(index.len(), 2);
//! assert_eq!(index.get("key1").unwrap(), "value1".to_string());
//! let new_index = index.remove("key1");
//! assert_eq!(index.get("key1").unwrap(), "value1".to_string());
//! assert_eq!(new_index.get("key1").is_none(), true);
//! ```
//!
//! [wiki-llrb]: https://en.wikipedia.org/wiki/Left-leaning_red-black_tree
//! [pds]: https://en.wikipedia.org/wiki/Persistent_data_structure
//! [im]: https://github.com/bodil/im-rs

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

pub mod arc;
mod mdb;
mod node;
mod omap;
mod op;
pub mod rc;

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
