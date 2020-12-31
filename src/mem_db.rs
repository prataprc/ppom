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
// *seqno*, application can set the beginning sequence number before
// ingesting data into the index.
//
// [llrb]: https://en.wikipedia.org/wiki/Left-leaning_red-black_tree
// [mvcc]: https://en.wikipedia.org/wiki/Multiversion_concurrency_control
// [LSM mode]: https://en.wikipedia.org/wiki/Log-structured_merge-tree

use mkit::{data::Diff, db, spinlock::Spinlock};

use std::{
    borrow::Borrow,
    cmp::{self, Ordering},
    sync::{Arc, Mutex},
};

use crate::{node::Node, op::Write, Error, Result};

/// Mdb type for thread-safe, concurrent reads and serialized writes.
///
/// [mvcc]: https://en.wikipedia.org/wiki/Multiversion_concurrency_control
/// [llrb]: https://en.wikipedia.org/wiki/Left-leaning_red-black_tree
#[derive(Clone)]
pub struct Mdb<K, V, D> {
    name: String,

    mu: Arc<Mutex<u32>>,
    inner: Arc<Spinlock<Arc<Inner<K, V, D>>>>,
}

//impl<K, V, D> TryFrom<Omap<K, V>> for Mdb<K, V, D> {
//    fn try_from(m: Omap<K, V>) -> Self {
//        todo!()
//    }
//}

impl<K, V, D> Mdb<K, V, D> {
    pub fn new(name: &str) -> Mdb<K, V, D> {
        let inner = Inner {
            root: None,
            seqno: 0,
            n_count: 0,
            n_deleted: 0,
        };

        Mdb {
            name: name.to_string(),
            mu: Arc::new(Mutex::new(0)),
            inner: Arc::new(Spinlock::new(Arc::new(inner))),
        }
    }
}

impl<K, V, D> Mdb<K, V, D> {
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

pub struct Wr<K, V, D> {
    pub seqno: u64,
    pub old_entry: Option<db::Entry<K, V, D>>,
}

impl<K, V, D> Mdb<K, V, D> {
    pub fn write(&self, op: Write<K, V>) -> Result<Wr<K, V, D>>
    where
        K: Clone + Ord,
        V: Clone + Diff<Delta = D>,
        D: Clone,
        <V as Diff>::Delta: From<V>,
    {
        let _w = self.mu.lock();

        let inner = Arc::clone(&self.inner.read());
        let (inner, old_entry) = match op {
            Write::Set {
                key,
                value,
                cas,
                seqno,
            } => inner.set((key, value, cas, seqno))?.into_root(),
            Write::Ins {
                key,
                value,
                cas,
                seqno,
            } => inner.insert((key, value, cas, seqno))?.into_root(),
            Write::Rem { key, cas, seqno } => {
                inner.remove((&key, cas, seqno))?.into_root()
            }
            Write::Del { key, cas, seqno } => {
                inner.delete((&key, cas, seqno))?.into_root()
            }
        };

        let seqno = inner.seqno;
        *self.inner.write() = Arc::new(inner);

        Ok(Wr { seqno, old_entry })
    }

    pub fn set(&self, key: K, value: V) -> Result<Wr<K, V, D>>
    where
        K: Clone + Ord,
        V: Clone,
        D: Clone,
    {
        let _w = self.mu.lock();

        let inner = Arc::clone(&self.inner.read());
        let op = (key, value, None, None);
        let (inner, old_entry) = inner.set(op)?.into_root();
        let seqno = inner.seqno;
        *self.inner.write() = Arc::new(inner);

        Ok(Wr { seqno, old_entry })
    }

    pub fn set_cas(&self, key: K, value: V, cas: u64) -> Result<Wr<K, V, D>>
    where
        K: Clone + Ord,
        V: Clone,
        D: Clone,
    {
        let _w = self.mu.lock();

        let inner = Arc::clone(&self.inner.read());
        let op = (key, value, Some(cas), None);
        let (inner, old_entry) = inner.set(op)?.into_root();
        let seqno = inner.seqno;
        *self.inner.write() = Arc::new(inner);

        Ok(Wr { seqno, old_entry })
    }

    pub fn insert(&self, key: K, value: V) -> Result<Wr<K, V, D>>
    where
        K: Clone + Ord,
        V: Clone + Diff<Delta = D>,
        D: Clone,
    {
        let _w = self.mu.lock();

        let inner = Arc::clone(&self.inner.read());
        let op = (key, value, None, None);
        let (inner, old_entry) = inner.insert(op)?.into_root();
        let seqno = inner.seqno;
        *self.inner.write() = Arc::new(inner);

        Ok(Wr { seqno, old_entry })
    }

    pub fn insert_cas(&self, key: K, value: V, cas: u64) -> Result<Wr<K, V, D>>
    where
        K: Clone + Ord,
        V: Clone + Diff<Delta = D>,
        D: Clone,
    {
        let _w = self.mu.lock();

        let inner = Arc::clone(&self.inner.read());
        let op = (key, value, Some(cas), None);
        let (inner, old_entry) = inner.insert(op)?.into_root();
        let seqno = inner.seqno;
        *self.inner.write() = Arc::new(inner);

        Ok(Wr { seqno, old_entry })
    }

    pub fn remove<Q>(&self, key: &Q) -> Result<Wr<K, V, D>>
    where
        K: Clone + Ord + Borrow<Q>,
        Q: Ord + ToOwned<Owned = K> + ?Sized,
        V: Clone,
        D: Clone,
    {
        let _w = self.mu.lock();

        let inner = Arc::clone(&self.inner.read());
        let op = (key, None, None);
        let (inner, old_entry) = inner.remove(op)?.into_root();
        let seqno = inner.seqno;
        *self.inner.write() = Arc::new(inner);

        Ok(Wr { seqno, old_entry })
    }

    pub fn remove_cas<Q>(&self, key: &Q, cas: u64) -> Result<Wr<K, V, D>>
    where
        K: Clone + Ord + Borrow<Q>,
        Q: Ord + ToOwned<Owned = K> + ?Sized,
        V: Clone,
        D: Clone,
    {
        let _w = self.mu.lock();

        let inner = Arc::clone(&self.inner.read());
        let op = (key, Some(cas), None);
        let (inner, old_entry) = inner.remove(op)?.into_root();
        let seqno = inner.seqno;
        *self.inner.write() = Arc::new(inner);

        Ok(Wr { seqno, old_entry })
    }

    pub fn delete<Q>(&self, key: &Q) -> Result<Wr<K, V, D>>
    where
        K: Clone + Ord + Borrow<Q>,
        Q: Ord + ToOwned<Owned = K> + ?Sized,
        V: Clone + Diff<Delta = D>,
        D: Clone,
        <V as Diff>::Delta: From<V>,
    {
        let _w = self.mu.lock();

        let inner = Arc::clone(&self.inner.read());
        let op = (key, None, None);
        let (inner, old_entry) = inner.delete(op)?.into_root();
        let seqno = inner.seqno;
        *self.inner.write() = Arc::new(inner);

        Ok(Wr { seqno, old_entry })
    }

    pub fn delete_cas<Q>(&self, key: &Q, cas: u64) -> Result<Wr<K, V, D>>
    where
        K: Clone + Ord + Borrow<Q>,
        Q: Ord + ToOwned<Owned = K> + ?Sized,
        V: Clone + Diff<Delta = D>,
        D: Clone,
        <V as Diff>::Delta: From<V>,
    {
        let _w = self.mu.lock();

        let inner = Arc::clone(&self.inner.read());
        let op = (key, Some(cas), None);
        let (inner, old_entry) = inner.delete(op)?.into_root();
        let seqno = inner.seqno;
        *self.inner.write() = Arc::new(inner);

        Ok(Wr { seqno, old_entry })
    }
}

macro_rules! compute_n_count {
    ($old:expr, $olde:expr) => {
        $old + $olde.map(|_| 0).unwrap_or(1)
    };
}

macro_rules! compute_n_deleted {
    ($old:expr, $olde:expr) => {
        $old.saturating_sub(
            $olde
                .map(|e| if e.is_deleted() { 1 } else { 0 })
                .unwrap_or(0),
        )
    };
}

#[derive(Clone)]
struct Inner<K, V, D> {
    root: Option<Arc<Node<K, V, D>>>,
    seqno: u64,
    n_count: usize,
    n_deleted: usize,
}

enum Ir<K, V, D> {
    Root {
        inner: Inner<K, V, D>,
        old: Option<db::Entry<K, V, D>>,
    },
    Res {
        root: Option<Arc<Node<K, V, D>>>,
        old: Option<db::Entry<K, V, D>>,
    },
}

impl<K, V, D> Ir<K, V, D> {
    fn into_root(self) -> (Inner<K, V, D>, Option<db::Entry<K, V, D>>) {
        match self {
            Ir::Root { inner, old } => (inner, old),
            _ => unreachable!(),
        }
    }

    fn into_res(self) -> (Option<Arc<Node<K, V, D>>>, Option<db::Entry<K, V, D>>) {
        match self {
            Ir::Res { root, old } => (root, old),
            _ => unreachable!(),
        }
    }
}

impl<K, V, D> Inner<K, V, D> {
    fn set(&self, op: (K, V, Option<u64>, Option<u64>)) -> Result<Ir<K, V, D>>
    where
        K: Clone + Ord,
        V: Clone,
        D: Clone,
    {
        let (key, value, cas, seqno) = op;
        let seqno = seqno.unwrap_or(self.seqno.saturating_add(1));
        let root = self.root.as_ref().map(Borrow::borrow);

        let op = (key, value, cas, seqno);
        let (mut root, old) = self.do_set(root, op)?.into_res();

        root.as_mut()
            .map(|root| Arc::get_mut(root).map(Node::set_black));

        let n_count = compute_n_count!(self.n_count, old.as_ref());
        let n_deleted = compute_n_deleted!(self.n_deleted, old.as_ref());

        let inner = Inner {
            root,
            seqno: cmp::max(self.seqno, seqno),
            n_count,
            n_deleted,
        };

        Ok(Ir::Root { inner, old })
    }

    fn insert(&self, op: (K, V, Option<u64>, Option<u64>)) -> Result<Ir<K, V, D>>
    where
        K: Clone + Ord,
        V: Clone + Diff<Delta = D>,
        D: Clone,
    {
        let (key, value, cas, seqno) = op;
        let seqno = seqno.unwrap_or(self.seqno.saturating_add(1));
        let root = self.root.as_ref().map(Borrow::borrow);

        let op = (key, value, cas, seqno);
        let (mut root, old) = self.do_insert(root, op)?.into_res();

        root.as_mut()
            .map(|root| Arc::get_mut(root).map(Node::set_black));

        let n_count = compute_n_count!(self.n_count, old.as_ref());
        let n_deleted = compute_n_deleted!(self.n_deleted, old.as_ref());

        let inner = Inner {
            root,
            seqno: cmp::max(self.seqno, seqno),
            n_count,
            n_deleted,
        };

        Ok(Ir::Root { inner, old })
    }

    fn remove<Q>(&self, op: (&Q, Option<u64>, Option<u64>)) -> Result<Ir<K, V, D>>
    where
        K: Clone + Borrow<Q>,
        Q: Ord + ToOwned<Owned = K> + ?Sized,
        V: Clone,
        D: Clone,
    {
        let (key, cas, seqno) = op;
        let seqno = seqno.unwrap_or(self.seqno.saturating_add(1));
        let root = self.root.as_ref().map(Borrow::borrow);

        let (mut root, old) = self.do_remove(root, (key, cas, seqno))?.into_res();

        root.as_mut()
            .map(|root| Arc::get_mut(root).map(Node::set_black));

        let (n_count, n_deleted) = if old.is_some() {
            (self.n_count - 1, self.n_deleted)
        } else {
            (self.n_count, self.n_deleted)
        };

        let inner = Inner {
            root: root,
            seqno: cmp::max(self.seqno, seqno),
            n_count,
            n_deleted,
        };

        Ok(Ir::Root { inner, old })
    }

    fn delete<Q>(&self, op: (&Q, Option<u64>, Option<u64>)) -> Result<Ir<K, V, D>>
    where
        K: Clone + Borrow<Q>,
        Q: Ord + ToOwned<Owned = K> + ?Sized,
        V: Clone + Diff<Delta = D>,
        D: Clone,
        <V as Diff>::Delta: From<V>,
    {
        let (key, cas, seqno) = op;
        let seqno = seqno.unwrap_or(self.seqno.saturating_add(1));
        let root = self.root.as_ref().map(Borrow::borrow);

        let (mut root, old) = self.do_delete(root, (key, cas, seqno))?.into_res();

        root.as_mut()
            .map(|root| Arc::get_mut(root).map(Node::set_black));

        let (n_count, n_deleted) = match old.as_ref() {
            Some(old) if !old.is_deleted() => (self.n_count, self.n_deleted + 1),
            Some(_) => (self.n_count, self.n_deleted),
            None => (self.n_count + 1, self.n_deleted + 1),
        };

        let inner = Inner {
            root: root,
            seqno: cmp::max(self.seqno, seqno),
            n_count,
            n_deleted,
        };

        Ok(Ir::Root { inner, old })
    }

    fn do_set(
        &self,
        node: Option<&Node<K, V, D>>,
        op: (K, V, Option<u64>, u64),
    ) -> Result<Ir<K, V, D>>
    where
        K: Clone + Ord,
        V: Clone,
        D: Clone,
    {
        let mut node: Node<K, V, D> = match (node, op.2) {
            (Some(node), _) => node.clone(),
            (None, Some(0)) | (None, None) => {
                let (key, value, _, seqno) = op;
                let node = db::Entry::new(key, value, seqno).into();
                let (root, old) = (Some(Arc::new(node)), None);
                return Ok(Ir::Res { root, old });
            }
            (None, Some(_)) => err_at!(InvalidCAS, msg: "invalid cas for missing set")?,
        };

        let cas = op.2;
        let (node, old) = match node.as_key().cmp(&op.0) {
            Ordering::Greater => {
                let left = node.left.as_ref().map(Borrow::borrow);
                let (root, old) = self.do_set(left, op)?.into_res();
                node.left = root;
                (walkuprot_23(node), old)
            }
            Ordering::Less => {
                let right = node.right.as_ref().map(Borrow::borrow);
                let (root, old) = self.do_set(right, op)?.into_res();
                node.right = root;
                (walkuprot_23(node), old)
            }
            Ordering::Equal if cas.is_none() || cas.unwrap() == node.to_seqno() => {
                let (_, value, _, seqno) = op;
                let old = node.entry.clone();
                node.set(value, seqno);
                (node, Some(old))
            }
            Ordering::Equal => {
                err_at!(InvalidCAS, msg: "{:?} != {}", cas, node.to_seqno())?
            }
        };
        let root = Some(Arc::new(node));

        Ok(Ir::Res { root, old })
    }

    fn do_insert(
        &self,
        node: Option<&Node<K, V, D>>,
        op: (K, V, Option<u64>, u64),
    ) -> Result<Ir<K, V, D>>
    where
        K: Clone + Ord,
        V: Clone + Diff<Delta = D>,
        D: Clone,
    {
        let mut node: Node<K, V, D> = match (node, op.2) {
            (Some(node), _) => node.clone(),
            (None, Some(0)) | (None, None) => {
                let (key, value, _, seqno) = op;
                let node = db::Entry::new(key, value, seqno).into();
                let (root, old) = (Some(Arc::new(node)), None);
                return Ok(Ir::Res { root, old });
            }
            (None, Some(_)) => err_at!(InvalidCAS, msg: "invalid cas for missing set")?,
        };

        let cas = op.2;
        let (node, old) = match node.as_key().cmp(&op.0) {
            Ordering::Greater => {
                let left = node.left.as_ref().map(Borrow::borrow);
                let (root, old) = self.do_insert(left, op)?.into_res();
                node.left = root;
                (walkuprot_23(node), old)
            }
            Ordering::Less => {
                let right = node.right.as_ref().map(Borrow::borrow);
                let (root, old) = self.do_insert(right, op)?.into_res();
                node.right = root;
                (walkuprot_23(node), old)
            }
            Ordering::Equal if cas.is_none() || cas.unwrap() == node.to_seqno() => {
                let (_, value, _, seqno) = op;
                let old = node.entry.clone();
                node.insert(value, seqno);
                (node, Some(old))
            }
            Ordering::Equal => {
                err_at!(InvalidCAS, msg: "{:?} != {}", cas, node.to_seqno())?
            }
        };
        let root = Some(Arc::new(node));

        Ok(Ir::Res { root, old })
    }

    fn do_remove<Q>(
        &self,
        node: Option<&Node<K, V, D>>,
        op: (&Q, Option<u64>, u64),
    ) -> Result<Ir<K, V, D>>
    where
        K: Clone + Borrow<Q>,
        Q: Ord + ToOwned<Owned = K> + ?Sized,
        V: Clone,
        D: Clone,
    {
        let (key, cas, _) = op.clone();

        let mut node: Node<K, V, D> = match (node, cas) {
            (Some(node), _) => node.clone(),
            (None, Some(0)) | (None, None) => {
                let (root, old) = (None, None);
                return Ok(Ir::Res { root, old });
            }
            (None, Some(_)) => err_at!(InvalidCAS, msg: "invalid cas for missing set")?,
        };

        let try_rotate_right = |node: Node<K, V, D>| -> Node<K, V, D> {
            match is_red(node.as_left_deref()) {
                true => rotate_right(node),
                false => node,
            }
        };

        let try_move_red_right = |node: Node<K, V, D>| -> Node<K, V, D> {
            match node.as_right_deref() {
                r @ Some(_) if !is_red(r) && !is_red(r.unwrap().as_left_deref()) => {
                    move_red_right(node)
                }
                Some(_) | None => node,
            }
        };

        let cas_ok = cas.is_none() || cas.unwrap() == node.to_seqno();

        let (root, old) = match node.as_key().borrow().cmp(key) {
            Ordering::Greater if node.left.is_none() && cas_ok => (Some(node), None),
            Ordering::Greater if node.left.is_none() => {
                err_at!(InvalidCAS, msg: "{} != {:?}", node.to_seqno(), cas)?
            }
            Ordering::Greater => {
                {
                    let left = node.as_left_deref();
                    if !is_red(left) && !is_red(left.unwrap().as_left_deref()) {
                        node = move_red_left(node)
                    }
                }

                let left = node.as_left_deref();
                let (root, old) = self.do_remove(left, op)?.into_res();
                node.left = root;
                (Some(fixup(node)), old)
            }
            Ordering::Less => {
                node = try_move_red_right(try_rotate_right(node));

                let right = node.as_right_deref();
                let (root, old) = self.do_remove(right, op)?.into_res();
                node.right = root;
                (Some(fixup(node)), old)
            }
            Ordering::Equal if node.right.is_none() && cas_ok => {
                node = try_rotate_right(node);
                (None, Some(node.entry.clone()))
            }
            Ordering::Equal if node.right.is_none() => {
                err_at!(InvalidCAS, msg: "{} != {:?}", node.to_seqno(), cas)?
            }
            Ordering::Equal if cas_ok => {
                node = try_move_red_right(try_rotate_right(node));
                let [right, sub_node] = self.do_remove_min(node.as_right_deref());
                node.right = right.map(Arc::new);
                let mut sub_node = match sub_node {
                    Some(sub_node) => sub_node,
                    None => return err_at!(Fatal, msg: "call the programmer"),
                };
                sub_node.left = node.left;
                sub_node.right = node.right;
                sub_node.black = node.black;
                (Some(fixup(sub_node)), Some(node.entry.clone()))
            }
            Ordering::Equal => {
                err_at!(InvalidCAS, msg: "{} != {:?}", node.to_seqno(), cas)?
            }
        };
        let root = root.map(Arc::new);

        Ok(Ir::Res { root, old })
    }

    fn do_delete<Q>(
        &self,
        node: Option<&Node<K, V, D>>,
        op: (&Q, Option<u64>, u64),
    ) -> Result<Ir<K, V, D>>
    where
        K: Clone + Borrow<Q>,
        Q: Ord + ToOwned<Owned = K> + ?Sized,
        V: Clone + Diff<Delta = D>,
        D: Clone,
        <V as Diff>::Delta: From<V>,
    {
        let (key, cas, seqno) = op.clone();

        let mut node: Node<K, V, D> = match (node, cas) {
            (Some(node), _) => node.clone(),
            (None, Some(0)) | (None, None) => {
                let key: K = key.to_owned();
                let (node, old) = (db::Entry::new_deleted(key, seqno).into(), None);
                let root = Some(Arc::new(node));
                return Ok(Ir::Res { root, old });
            }
            (None, Some(_)) => err_at!(InvalidCAS, msg: "invalid cas for missing set")?,
        };

        let cas_ok = cas.is_none() || cas.unwrap() == node.to_seqno();

        let (root, old) = match node.as_key().borrow().cmp(key) {
            Ordering::Greater => {
                let left = node.as_left_deref();
                let (root, old) = self.do_delete(left, op)?.into_res();
                node.left = root;
                (Some(walkuprot_23(node)), old)
            }
            Ordering::Less => {
                let right = node.as_right_deref();
                let (root, old) = self.do_delete(right, op)?.into_res();
                node.right = root;
                (Some(walkuprot_23(node)), old)
            }
            Ordering::Equal if cas_ok => {
                let old = node.entry.clone();
                node.delete(seqno);
                (Some(walkuprot_23(node)), Some(old))
            }
            Ordering::Equal => {
                err_at!(InvalidCAS, msg: "{} != {:?}", node.to_seqno(), cas)?
            }
        };
        let root = root.map(Arc::new);

        Ok(Ir::Res { root, old })
    }

    fn do_remove_min(&self, node: Option<&Node<K, V, D>>) -> [Option<Node<K, V, D>>; 2]
    where
        K: Clone,
        V: Clone,
        D: Clone,
    {
        let mut node = match node {
            Some(node) => node.clone(),
            None => return [None, None],
        };

        if node.left.is_none() {
            return [None, Some(node)];
        }

        let left = node.as_left_deref();

        if !is_red(left) && !is_red(left.unwrap().as_left_deref()) {
            node = move_red_left(node);
        }
        let [left, sub_node] = self.do_remove_min(node.as_left_deref());
        node.left = left.map(Arc::new);
        [Some(fixup(node)), sub_node]
    }
}

#[inline]
fn is_red<K, V, D>(node: Option<&Node<K, V, D>>) -> bool {
    node.map_or(false, |node| !node.is_black())
}

#[inline]
fn is_black<K, V, D>(node: Option<&Node<K, V, D>>) -> bool {
    node.map_or(true, Node::is_black)
}

fn walkuprot_23<K, V, D>(mut node: Node<K, V, D>) -> Node<K, V, D>
where
    K: Clone,
    V: Clone,
    D: Clone,
{
    if is_red(node.as_right_deref()) && !is_red(node.as_left_deref()) {
        node = rotate_left(node)
    }
    let left = node.as_left_deref();
    if is_red(left) && is_red(left.unwrap().as_left_deref()) {
        node = rotate_right(node);
    }
    if is_red(node.as_left_deref()) && is_red(node.as_right_deref()) {
        flip(&mut node)
    }
    node
}

//              (i)                       (i)
//               |                         |
//              node                     right
//              /  \                      / \
//             /    (r)                 (r)  \
//            /       \                 /     \
//          left     right           node     r-r
//                    / \            /  \
//                 r-l  r-r       left  r-l
//
fn rotate_left<K, V, D>(mut node: Node<K, V, D>) -> Node<K, V, D>
where
    K: Clone,
    V: Clone,
    D: Clone,
{
    let old_right: &Node<K, V, D> = node.right.as_ref().map(|r| r.borrow()).unwrap();
    if is_black(Some(old_right)) {
        panic!("rotateleft(): rotate black link ? call-the-programmer");
    }

    let mut right = old_right.clone();

    node.right = right.left.take();
    right.black = node.black;
    node.set_red();
    right.left = Some(Arc::new(node));

    right
}

//              (i)                       (i)
//               |                         |
//              node                      left
//              /  \                      / \
//            (r)   \                   (r)  \
//           /       \                 /      \
//         left     right            l-l      node
//         / \                                / \
//      l-l  l-r                            l-r  right
//
fn rotate_right<K, V, D>(mut node: Node<K, V, D>) -> Node<K, V, D>
where
    K: Clone,
    V: Clone,
    D: Clone,
{
    let old_left: &Node<K, V, D> = node.left.as_ref().map(|r| r.borrow()).unwrap();
    if is_black(Some(old_left)) {
        panic!("rotateright(): rotate black link ? call-the-programmer")
    }

    let mut left = old_left.clone();

    node.left = left.right.take();
    left.black = node.black;
    node.set_red();
    left.right = Some(Arc::new(node));

    left
}

//        (x)                   (!x)
//         |                     |
//        node                  node
//        / \                   / \
//      (y) (z)              (!y) (!z)
//     /      \              /      \
//   left    right         left    right
//
fn flip<K, V, D>(node: &mut Node<K, V, D>)
where
    K: Clone,
    V: Clone,
    D: Clone,
{
    let mut left = {
        let left: &Node<K, V, D> = node.left.as_ref().map(|l| l.borrow()).unwrap();
        left.clone()
    };
    let mut right = {
        let right: &Node<K, V, D> = node.right.as_ref().map(|r| r.borrow()).unwrap();
        right.clone()
    };

    node.toggle_link();
    left.toggle_link();
    right.toggle_link();

    node.left = Some(Arc::new(left));
    node.right = Some(Arc::new(right));
}

fn fixup<K, V, D>(mut node: Node<K, V, D>) -> Node<K, V, D>
where
    K: Clone,
    V: Clone,
    D: Clone,
{
    if is_red(node.as_right_deref()) {
        node = rotate_left(node)
    }
    let left = node.as_left_deref();
    if is_red(left) && is_red(left.unwrap().as_left_deref()) {
        node = rotate_right(node)
    }
    if is_red(node.as_left_deref()) && is_red(node.as_right_deref()) {
        flip(&mut node)
    }
    node
}

fn move_red_left<K, V, D>(mut node: Node<K, V, D>) -> Node<K, V, D>
where
    K: Clone,
    V: Clone,
    D: Clone,
{
    flip(&mut node);

    if is_red(node.right.as_ref().unwrap().as_left_deref()) {
        let right = node.right.take().unwrap();
        let newr = {
            let rr: &Node<K, V, D> = right.borrow();
            rr.clone()
        };
        node.right = Some(Arc::new(rotate_right(newr)));
        node = rotate_left(node);
        flip(&mut node);
    }
    node
}

fn move_red_right<K, V, D>(mut node: Node<K, V, D>) -> Node<K, V, D>
where
    K: Clone,
    V: Clone,
    D: Clone,
{
    flip(&mut node);

    if is_red(node.left.as_ref().unwrap().as_left_deref()) {
        node = rotate_right(node);
        flip(&mut node);
    }
    node
}
