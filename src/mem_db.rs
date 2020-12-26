// Module ``mvcc`` implement [Multi-Version-Concurrency-Control][mvcc]
// variant of [Llrb].
//
// [Mvcc] type allow concurrent read and write access at API level,
// while behind the scenes, all write-operations are serialized into
// single thread, but the key difference is that [Mvcc] index allow
// concurrent-reads without using locks. To serialize concurrent writes
// [Mvcc] uses a spin-lock implementation that can be configured to
// _yield_ or _spin_ while waiting for the lock.
//
// **[LSM mode]**: Mvcc index can support log-structured-merge while
// mutating the tree. In simple terms, this means that nothing shall be
// over-written in the tree and all the mutations for the same key shall
// be preserved until they are purged.
//
// **Possible ways to configure Mvcc**:
//
// *spinlatch*, relevant only in multi-threaded context. Calling
// _set_spinlatch()_ with _true_ will have the calling thread to spin
// while waiting to acquire the lock. Calling it with _false_ will have the
// calling thread to yield to OS scheduler while waiting to acquire the lock.
//
// *sticky*, is a shallow variant of lsm, applicable only when
// `lsm` option is disabled. For more information refer to Mvcc::set_sticky()
// method.
//
// *seqno*, application can set the beginning sequence number before
// ingesting data into the index.
//
// [llrb]: https://en.wikipedia.org/wiki/Left-leaning_red-black_tree
// [mvcc]: https://en.wikipedia.org/wiki/Multiversion_concurrency_control
// [LSM mode]: https://en.wikipedia.org/wiki/Log-structured_merge-tree

use mkit::{db, spinlock::Spinlock};

use std::sync::{Arc, Mutex};

use crate::{node::Node, Error, Result};

/// Mdb type for thread-safe, concurrent reads and serialized writes.
///
/// [mvcc]: https://en.wikipedia.org/wiki/Multiversion_concurrency_control
/// [llrb]: https://en.wikipedia.org/wiki/Left-leaning_red-black_tree
#[derive(Clone)]
pub struct Mdb<K, V, D> {
    name: String,
    lsm: bool,
    sticky: bool,

    mu: Arc<Mutex<u32>>,
    inner: Arc<Spinlock<Arc<Inner<K, V, D>>>>,
}

//impl<K, V, D> TryFrom<Omap<K, V>> for Mdb<K, V, D> {
//    fn try_from(m: Omap<K, V>) -> Self {
//        todo!()
//    }
//}

impl<K, V, D> Mdb<K, V, D> {
    fn new(name: &str, lsm: bool, sticky: bool) -> Mdb<K, V, D> {
        let inner = Inner {
            lsm,
            sticky,

            root: None,
            seqno: 0,
            n_count: 0,
            n_deleted: 0,
        };

        Mdb {
            name: name.to_string(),
            lsm,
            sticky,

            mu: Arc::new(Mutex::new(0)),
            inner: Arc::new(Spinlock::new(Arc::new(inner))),
        }
    }
}

impl<K, V, D> Mdb<K, V, D> {
    /// Return whether this index is in lsm mode.
    #[inline]
    pub fn is_lsm(&self) -> bool {
        self.lsm
    }

    /// Return whether this index is in sticky mode.
    #[inline]
    pub fn is_sticky(&self) -> bool {
        self.sticky
    }

    /// Return number of entries in this instance.
    pub fn len(&self) -> usize {
        let inner = Arc::clone(&self.inner.read());
        inner.n_count
    }

    /// Return whether the index is empty.
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Return the current sequence-no for this index.
    pub fn to_seqno(&self) -> u64 {
        let inner = Arc::clone(&self.inner.read());
        inner.seqno
    }

    /// Update index to a new sequence-no, future mutations shall start
    /// from this value.
    pub fn set_seqno(&self, seqno: u64) -> u64
    where
        K: Clone,
        V: Clone,
        D: Clone,
    {
        let (mut inner, old_seqno) = {
            let inner = Arc::clone(&self.inner.read());
            (inner.as_ref().clone(), inner.seqno)
        };

        inner.seqno = seqno;
        *self.inner.write() = Arc::new(inner);

        old_seqno
    }

    /// Identify this index instance.
    #[inline]
    pub fn to_name(&self) -> String {
        self.name.clone()
    }

    pub fn commit() -> Result<()> {
        todo!()
    }

    pub fn compact() -> Result<usize> {
        todo!()
    }

    pub fn close(self) -> Result<()> {
        Ok(())
    }
}

pub enum Op<K, V> {
    Set {
        key: K,
        value: V,
        seqno: u64,
    },
    Cas {
        key: K,
        value: V,
        cas: u64,
        seqno: u64,
    },
}

pub struct Wr<K, V, D> {
    seqno: u64,
    old_entry: Option<db::Entry<K, V, D>>,
}

impl<K, V, D> Mdb<K, V, D> {
    pub fn write(&self, op: Op<K, V>) -> Result<Wr<K, V, D>> {
        let _w = self.mu.lock();

        let inner = Arc::clone(&self.inner.read());
        let (inner, old_entry) = match op {
            Op::Set { key, value, seqno } => match inner.set(key, value, Some(seqno))? {
                Ir::Res { inner, node, old } => (inner, old),
                _ => unreachable!(),
            },
            Op::Cas {
                key,
                value,
                cas,
                seqno,
            } => match inner.set_cas(key, value, cas, Some(seqno))? {
                Ir::Res { inner, node, old } => (inner, old),
                _ => unreachable!(),
            },
        };

        let seqno = inner.seqno;
        *self.inner.write() = Arc::new(inner);

        Ok(Wr { seqno, old_entry })
    }

    pub fn set(&self, key: K, value: V) -> Result<Wr<K, V, D>> {
        let _w = self.mu.lock();

        let inner = Arc::clone(&self.inner.read());
        match inner.set(key, value, None)? {
            Ir::Res { inner, node, old } => {
                let old_entry = old;
                let seqno = inner.seqno;
                *self.inner.write() = Arc::new(inner);
                Ok(Wr { seqno, old_entry })
            }
            _ => unreachable!(),
        }
    }

    pub fn set_cas(&self, key: K, value: V, cas: u64) -> Result<Wr<K, V, D>> {
        let _w = self.mu.lock();

        let inner = Arc::clone(&self.inner.read());
        match inner.set_cas(key, value, cas, None)? {
            Ir::Res { inner, node, old } => {
                let old_entry = old;
                let seqno = inner.seqno;
                *self.inner.write() = Arc::new(inner);
                Ok(Wr { seqno, old_entry })
            }
            _ => unreachable!(),
        }
    }
}

#[derive(Clone)]
struct Inner<K, V, D> {
    lsm: bool,
    sticky: bool,

    root: Option<Node<K, V, D>>,
    seqno: u64,
    n_count: usize,
    n_deleted: usize,
}

enum Ir<K, V, D> {
    Res {
        inner: Inner<K, V, D>,
        node: Option<Node<K, V, D>>,
        old: Option<db::Entry<K, V, D>>,
    },
    Set {
        root: Node<K, V, D>,
        node: Option<Node<K, V, D>>,
        old: Option<db::Entry<K, V, D>>,
    },
    Cas {
        root: Node<K, V, D>,
        node: Option<Node<K, V, D>>,
        old: Option<db::Entry<K, V, D>>,
    },
}

impl<K, V, D> Inner<K, V, D> {
    fn set(&self, key: K, value: V, seqno: Option<u64>) -> Result<Ir<K, V, D>> {
        let seqno = seqno.unwrap_or(self.seqno.saturating_add(1));

        let (mut root, node, old) = match &self.root {
            None => {
                let root: Node<K, V, D> = db::Entry::new(key, value, seqno).into();
                (root, None, None)
            }
            Some(root) => match self.do_set(root, value, seqno)? {
                Ir::Set { root, node, old } => (root, node, old),
                _ => unreachable!(),
            },
        };
        root.set_black();
        let n_count = self.n_count + old.as_ref().map(|_| 0).unwrap_or(1);
        let n_deleted = self.n_deleted.saturating_sub(
            old.as_ref()
                .map(|e| if e.is_deleted() { 1 } else { 0 })
                .unwrap_or(0),
        );

        let inner = Inner {
            lsm: self.lsm,
            sticky: self.sticky,

            root: Some(root),
            seqno,
            n_count,
            n_deleted,
        };

        Ok(Ir::Res { inner, node, old })
    }

    fn set_cas(
        &self,
        key: K,
        value: V,
        cas: u64,
        seqno: Option<u64>,
    ) -> Result<Ir<K, V, D>> {
        let seqno = seqno.unwrap_or(self.seqno.saturating_add(1));

        let (mut root, node, old) = match &self.root {
            None if cas == 0 => {
                let root: Node<K, V, D> = db::Entry::new(key, value, seqno).into();
                (root, None, None)
            }
            None => err_at!(InvalidCAS, msg: "empty index, CAS {}", cas)?,
            Some(root) => match self.do_set_cas(root, value, cas, seqno)? {
                Ir::Cas { root, node, old } => (root, node, old),
                _ => unreachable!(),
            },
        };
        root.set_black();
        let n_count = self.n_count + old.as_ref().map(|_| 0).unwrap_or(1);
        let n_deleted = self.n_deleted.saturating_sub(
            old.as_ref()
                .map(|e| if e.is_deleted() { 1 } else { 0 })
                .unwrap_or(0),
        );

        let inner = Inner {
            lsm: self.lsm,
            sticky: self.sticky,

            root: Some(root),
            seqno,
            n_count,
            n_deleted,
        };

        Ok(Ir::Res { inner, node, old })
    }

    fn do_set(&self, node: &Node<K, V, D>, value: V, seqno: u64) -> Result<Ir<K, V, D>> {
        todo!()
    }

    fn do_set_cas(
        &self,
        node: &Node<K, V, D>,
        value: V,
        cas: u64,
        seqno: u64,
    ) -> Result<Ir<K, V, D>> {
        todo!()
    }
}
