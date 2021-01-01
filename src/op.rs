#[allow(unused_imports)]
use crate::Mdb;

/// Write operations allowed on [Mdb] index.
///
/// There is a corresponding API exposed vi [Mdb] type. For
/// details refer to corresponding method. `cas` is optional where ever
/// it is applicable. Additionally, it is possible to set the sequence
/// number for each write-operation, which is useful to replaying operations
/// from external entities like Write-Ahead-Logs.
pub enum Write<K, V> {
    /// Refer to Mdb::set.
    Set {
        key: K,
        value: V,
        cas: Option<u64>,
        seqno: Option<u64>,
    },
    /// Refer to Mdb::insert.
    Ins {
        key: K,
        value: V,
        cas: Option<u64>,
        seqno: Option<u64>,
    },
    /// Refer to Mdb::delete.
    Del {
        key: K,
        cas: Option<u64>,
        seqno: Option<u64>,
    },
    /// Refer to Mdb::remove.
    Rem {
        key: K,
        cas: Option<u64>,
        seqno: Option<u64>,
    },
}

impl<K, V> Write<K, V> {
    /// Create a new `set` op.
    #[inline]
    pub fn set(key: K, value: V) -> Write<K, V> {
        Write::Set {
            key,
            value,
            cas: None,
            seqno: None,
        }
    }

    /// Create a new `insert` op.
    #[inline]
    pub fn insert(key: K, value: V) -> Write<K, V> {
        Write::Ins {
            key,
            value,
            cas: None,
            seqno: None,
        }
    }

    /// Create a new `remove` op.
    #[inline]
    pub fn remove(key: K) -> Write<K, V> {
        Write::Rem {
            key,
            cas: None,
            seqno: None,
        }
    }

    /// Create a new `delete` op.
    #[inline]
    pub fn delete(key: K) -> Write<K, V> {
        Write::Del {
            key,
            cas: None,
            seqno: None,
        }
    }

    /// Update op with seqno.
    pub fn set_seqno(self, seqno: u64) -> Write<K, V> {
        use Write::*;

        match self {
            Set {
                key, value, cas, ..
            } => Set {
                key,
                value,
                cas,
                seqno: Some(seqno),
            },
            Ins {
                key, value, cas, ..
            } => Ins {
                key,
                value,
                cas,
                seqno: Some(seqno),
            },
            Del { key, cas, .. } => Del {
                key,
                cas,
                seqno: Some(seqno),
            },
            Rem { key, cas, .. } => Rem {
                key,
                cas,
                seqno: Some(seqno),
            },
        }
    }

    /// Update op with cas.
    pub fn set_cas(self, cas: u64) -> Write<K, V> {
        use Write::*;

        match self {
            Set {
                key, value, seqno, ..
            } => Set {
                key,
                value,
                seqno,
                cas: Some(cas),
            },
            Ins {
                key, value, seqno, ..
            } => Ins {
                key,
                value,
                seqno,
                cas: Some(cas),
            },
            Del { key, seqno, .. } => Del {
                key,
                seqno,
                cas: Some(cas),
            },
            Rem { key, seqno, .. } => Rem {
                key,
                seqno,
                cas: Some(cas),
            },
        }
    }
}
