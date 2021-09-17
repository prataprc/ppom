//! Module implement partially-persistent ordered-map, slower but concurrent.

use std::{
    borrow::Borrow,
    cmp::{self, Ordering},
    fmt, marker,
    ops::{Bound, RangeBounds},
    sync::{Arc, Mutex},
};

use crate::{
    mdb_node::{Entry, Node},
    spinlock::Spinlock,
    Error, Result,
};

pub const MAX_TREE_DEPTH: usize = 100;

macro_rules! compute_n_count {
    ($old:expr, $olde:expr) => {
        $old + $olde.map(|_| 0).unwrap_or(1)
    };
}

/// Partially persistent ordered-map type using [left-leaning-red-black][llrb] tree.
///
/// [OMap] type allow concurrent read and write access at API level,
/// while behind the scenes, all write-operations are serialized into
/// single thread, but the key difference is that [OMap] map allow
/// concurrent-reads without using locks. To serialize concurrent writes
/// [OMap] uses a spin-lock implementation.
///
/// [llrb]: https://en.wikipedia.org/wiki/Left-leaning_red-black_tree
/// [mvcc]: https://en.wikipedia.org/wiki/Multiversion_concurrency_control
/// [LSM mode]: https://en.wikipedia.org/wiki/Log-structured_merge-tree
#[derive(Clone)]
pub struct OMap<K, V> {
    mu: Arc<Mutex<u32>>,
    inner: Arc<Spinlock<Arc<Inner<K, V>>>>,
}

impl<K, V> OMap<K, V> {
    pub fn new() -> OMap<K, V> {
        let inner = Inner {
            root: None,
            seqno: 0,
            n_count: 0,
        };

        OMap {
            mu: Arc::new(Mutex::new(0)),
            inner: Arc::new(Spinlock::new(Arc::new(inner))),
        }
    }
}

impl<K, V> OMap<K, V> {
    /// Return number of entries in this instance.
    pub fn len(&self) -> usize {
        let inner = Arc::clone(&self.inner.read());
        inner.n_count
    }

    /// Return whether index is empty.
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Return current sequence-no for index.
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
    {
        let (mut inner, old_seqno) = {
            let inner = Arc::clone(&self.inner.read());
            (inner.as_ref().clone(), inner.seqno)
        };

        inner.seqno = seqno;
        *self.inner.write() = Arc::new(inner);

        old_seqno
    }
}

impl<K, V> OMap<K, V> {
    /// Set `key`, `value` into index. If an older entry exist with same key,
    /// it shall be overwritten.
    pub fn set(&self, key: K, value: V) -> Result<Option<V>>
    where
        K: Clone + Ord,
        V: Clone,
    {
        let _w = self.mu.lock();

        let inner = Arc::clone(&self.inner.read());
        let op = (key, value, None, None);
        let (inner, old_value) = inner.set(op)?.into_root();
        *self.inner.write() = Arc::new(inner);

        Ok(old_value)
    }

    /// Set `key`, `value` into index. If already an entry in present with
    /// `key`, `cas` should match entry's sequence-number. If index don't
    /// have an entry with `key`, `cas` must be ZERO.
    pub fn set_cas(&self, key: K, value: V, cas: u64) -> Result<Option<V>>
    where
        K: Clone + Ord,
        V: Clone,
    {
        let _w = self.mu.lock();

        let inner = Arc::clone(&self.inner.read());
        let op = (key, value, Some(cas), None);
        let (inner, old_value) = inner.set(op)?.into_root();
        *self.inner.write() = Arc::new(inner);

        Ok(old_value)
    }

    /// Remove the entry, matching the key, from the index.
    pub fn remove<Q>(&self, key: &Q) -> Result<Option<V>>
    where
        K: Clone + Ord + Borrow<Q>,
        Q: Ord + ToOwned<Owned = K> + ?Sized,
        V: Clone,
    {
        let _w = self.mu.lock();

        let inner = Arc::clone(&self.inner.read());
        let op = (key, None, None);
        let (inner, old_value) = inner.remove(op)?.into_root();
        *self.inner.write() = Arc::new(inner);

        Ok(old_value)
    }

    /// Remove the entry, with matching key and matching entry's sequencey-number
    /// with `cas`.
    pub fn remove_cas<Q>(&self, key: &Q, cas: u64) -> Result<Option<V>>
    where
        K: Clone + Ord + Borrow<Q>,
        Q: Ord + ToOwned<Owned = K> + ?Sized,
        V: Clone,
    {
        let _w = self.mu.lock();

        let inner = Arc::clone(&self.inner.read());
        let op = (key, Some(cas), None);
        let (inner, old_value) = inner.remove(op)?.into_root();
        *self.inner.write() = Arc::new(inner);

        Ok(old_value)
    }
}

impl<K, V> OMap<K, V> {
    /// Get entry from index for `key`. An entry is returned as (value, seqno). If
    /// key is not found return [Error::KeyNotFound]
    pub fn get<Q>(&self, key: &Q) -> Result<(V, u64)>
    where
        K: Clone + Borrow<Q>,
        V: Clone,
        Q: Ord + ?Sized,
    {
        let inner = Arc::clone(&self.inner.read());
        inner.get(key)
    }

    /// For full table scan.
    pub fn iter(&self) -> Result<Iter<K, V>> {
        let inner = Arc::clone(&self.inner.read());
        Ok(inner.iter())
    }

    /// Iterate over entries within the specifed `range`.
    pub fn range<R, Q>(&self, range: R) -> Result<Range<K, V, R, Q>>
    where
        K: Borrow<Q>,
        R: RangeBounds<Q>,
        Q: Ord + ?Sized,
    {
        let inner = Arc::clone(&self.inner.read());
        Ok(inner.range(range))
    }

    /// Reverse iterate over entries withing specified `range`. While
    /// `range` method iterate entries from start_bound to end_bound
    /// `reverse` method iterate entries from end_bound to start_bound.
    pub fn reverse<R, Q>(&self, range: R) -> Result<Reverse<K, V, R, Q>>
    where
        K: Borrow<Q>,
        R: RangeBounds<Q>,
        Q: Ord + ?Sized,
    {
        let inner = Arc::clone(&self.inner.read());
        Ok(inner.reverse(range))
    }

    /// Validate [OMap] tree with following rules:
    ///
    /// * Root node is always black in color.
    /// * Verify the sort order between a node and its left/right child.
    /// * No node has RIGHT RED child and LEFT BLACK child (or NULL child).
    /// * Make sure there are no consecutive reds.
    /// * Make sure number of blacks are same on both left and right arm.
    /// * Make sure that the maximum depth do not exceed MAX_TREE_DEPTH.
    pub fn validate(&self) -> Result<()>
    where
        K: Ord + fmt::Debug,
    {
        let inner = Arc::clone(&self.inner.read());
        inner.validate()
    }
}

#[derive(Clone)]
struct Inner<K, V> {
    root: Option<Arc<Node<K, V>>>,
    seqno: u64,
    n_count: usize,
}

enum Ir<K, V> {
    Root {
        inner: Inner<K, V>,
        old: Option<Entry<V>>,
    },
    Res {
        root: Option<Arc<Node<K, V>>>,
        old: Option<Arc<Entry<V>>>,
    },
}

impl<K, V> Ir<K, V> {
    #[allow(clippy::type_complexity)]
    fn into_root(self) -> (Inner<K, V>, Option<V>) {
        match self {
            Ir::Root { inner, old } => (inner, old.map(|e| e.into_value())),
            _ => unreachable!(),
        }
    }

    #[allow(clippy::type_complexity)]
    fn into_res(self) -> (Option<Arc<Node<K, V>>>, Option<Arc<Entry<V>>>) {
        match self {
            Ir::Res { root, old } => (root, old),
            _ => unreachable!(),
        }
    }
}

impl<K, V> Inner<K, V> {
    fn set(&self, op: (K, V, Option<u64>, Option<u64>)) -> Result<Ir<K, V>>
    where
        K: Clone + Ord,
        V: Clone,
    {
        let (key, value, cas, seqno) = op;
        let seqno = seqno.unwrap_or_else(|| self.seqno.saturating_add(1));
        let root = self.root.as_ref().map(Borrow::borrow);

        let op = (key, value, cas, seqno);
        let (mut root, old) = self.do_set(root, op)?.into_res();

        root.as_mut()
            .map(|root| Arc::get_mut(root).map(Node::set_black));

        let n_count = compute_n_count!(self.n_count, old.as_ref());

        let inner = Inner {
            root,
            seqno: cmp::max(self.seqno, seqno),
            n_count,
        };

        let old = old.as_ref().map(|old| old.as_ref().clone());

        Ok(Ir::Root { inner, old })
    }

    fn remove<Q>(&self, op: (&Q, Option<u64>, Option<u64>)) -> Result<Ir<K, V>>
    where
        K: Clone + Borrow<Q>,
        Q: Ord + ToOwned<Owned = K> + ?Sized,
        V: Clone,
    {
        let (key, cas, seqno) = op;
        let seqno = seqno.unwrap_or_else(|| self.seqno.saturating_add(1));
        let root = self.root.as_ref().map(Borrow::borrow);

        let (mut root, old) = self.do_remove(root, (key, cas, seqno))?.into_res();

        root.as_mut()
            .map(|root| Arc::get_mut(root).map(Node::set_black));

        let (seqno, n_count) = if old.is_some() {
            (seqno, self.n_count - 1)
        } else {
            (self.seqno, self.n_count)
        };

        let inner = Inner {
            root,
            seqno: cmp::max(self.seqno, seqno),
            n_count,
        };

        let old = old.as_ref().map(|old| old.as_ref().clone());

        Ok(Ir::Root { inner, old })
    }

    fn do_set(
        &self,
        node: Option<&Node<K, V>>,
        op: (K, V, Option<u64>, u64),
    ) -> Result<Ir<K, V>>
    where
        K: Clone + Ord,
        V: Clone,
    {
        let mut node: Node<K, V> = match (node, op.2) {
            (Some(node), _) => node.clone(),
            (None, Some(0)) | (None, None) => {
                let (key, value, _, seqno) = op;
                let node = (key, Entry::new(value, seqno)).into();
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

    fn do_remove<Q>(
        &self,
        node: Option<&Node<K, V>>,
        op: (&Q, Option<u64>, u64),
    ) -> Result<Ir<K, V>>
    where
        K: Clone + Borrow<Q>,
        Q: Ord + ToOwned<Owned = K> + ?Sized,
        V: Clone,
    {
        let (key, cas, _) = op;

        let mut node: Node<K, V> = match (node, cas) {
            (Some(node), _) => node.clone(),
            (None, Some(0)) | (None, None) => {
                let (root, old) = (None, None);
                return Ok(Ir::Res { root, old });
            }
            (None, Some(_)) => err_at!(InvalidCAS, msg: "invalid cas for missing set")?,
        };

        let (root, old) = match node.as_key().borrow().cmp(key) {
            Ordering::Greater if node.left.is_none() => (Some(node), None),
            Ordering::Greater => {
                let left = node.as_left_ref();
                if !is_red(left) && !is_red(left.unwrap().as_left_ref()) {
                    node = move_red_left(node)
                }

                let (left, old) = self.do_remove(node.as_left_ref(), op)?.into_res();
                node.left = left;
                (Some(fixup(node)), old)
            }
            _ => {
                if is_red(node.as_left_ref()) {
                    node = rotate_right(node);
                }

                let cas_ok = cas.is_none() || cas.unwrap() == node.to_seqno();

                if node.as_key().borrow().eq(key) && !cas_ok {
                    err_at!(InvalidCAS, msg: "{} != {:?}", node.to_seqno(), cas)?;
                }

                if !node.as_key().borrow().lt(key) && node.right.is_none() {
                    (None, Some(node.entry.clone()))
                } else {
                    node = match node.as_right_ref() {
                        r @ Some(_)
                            if !is_red(r) && !is_red(r.unwrap().as_left_ref()) =>
                        {
                            move_red_right(node)
                        }
                        Some(_) | None => node,
                    };

                    if !node.as_key().borrow().lt(key) {
                        let [right, sub_node] = self.do_remove_min(node.as_right_ref());
                        node.right = right.map(Arc::new);
                        let mut sub_node = match sub_node {
                            Some(sub_node) => sub_node,
                            None => return err_at!(Fatal, msg: "call the programmer"),
                        };
                        sub_node.left = node.left;
                        sub_node.right = node.right;
                        sub_node.black = node.black;
                        (Some(fixup(sub_node)), Some(node.entry.clone()))
                    } else {
                        let right = node.as_right_ref();
                        let (right, old) = self.do_remove(right, op)?.into_res();
                        node.right = right;
                        (Some(fixup(node)), old)
                    }
                }
            }
        };
        let root = root.map(Arc::new);

        Ok(Ir::Res { root, old })
    }

    fn do_remove_min(&self, node: Option<&Node<K, V>>) -> [Option<Node<K, V>>; 2]
    where
        K: Clone,
        V: Clone,
    {
        let mut node = match node {
            Some(node) => node.clone(),
            None => return [None, None],
        };

        if node.left.is_none() {
            return [None, Some(node)];
        }

        let left = node.as_left_ref();

        if !is_red(left) && !is_red(left.unwrap().as_left_ref()) {
            node = move_red_left(node);
        }
        let [left, sub_node] = self.do_remove_min(node.as_left_ref());
        node.left = left.map(Arc::new);
        [Some(fixup(node)), sub_node]
    }
}

impl<K, V> Inner<K, V> {
    fn get<Q>(&self, key: &Q) -> Result<(V, u64)>
    where
        K: Clone + Borrow<Q>,
        V: Clone,
        Q: Ord + ?Sized,
    {
        let root = self.root.as_ref().map(Borrow::borrow);
        get(root, key)
    }

    fn iter(&self) -> Iter<K, V> {
        let root = self.root.as_ref().map(Arc::clone);
        let mut paths = Vec::default();
        build_iter(IFlag::Left, root, &mut paths);

        Iter { paths, frwrd: true }
    }

    fn range<R, Q>(&self, range: R) -> Range<K, V, R, Q>
    where
        K: Borrow<Q>,
        R: RangeBounds<Q>,
        Q: Ord + ?Sized,
    {
        let root = self.root.as_ref().map(Arc::clone);

        let mut paths = Vec::default();
        match range.start_bound() {
            Bound::Unbounded => build_iter(IFlag::Left, root, &mut paths),
            Bound::Included(low) => find_start(root, low, true, &mut paths),
            Bound::Excluded(low) => find_start(root, low, false, &mut paths),
        };
        let iter = Iter { paths, frwrd: true };

        Range {
            range,
            iter,
            fin: false,
            high: marker::PhantomData,
        }
    }

    fn reverse<R, Q>(&self, range: R) -> Reverse<K, V, R, Q>
    where
        K: Borrow<Q>,
        R: RangeBounds<Q>,
        Q: Ord + ?Sized,
    {
        let root = self.root.as_ref().map(Arc::clone);

        let mut paths = Vec::default();
        match range.end_bound() {
            Bound::Unbounded => build_iter(IFlag::Right, root, &mut paths),
            Bound::Included(high) => find_end(root, high, true, &mut paths),
            Bound::Excluded(high) => find_end(root, high, false, &mut paths),
        };
        let iter = Iter {
            paths,
            frwrd: false,
        };

        Reverse {
            range,
            iter,
            fin: false,
            low: marker::PhantomData,
        }
    }

    fn validate(&self) -> Result<()>
    where
        K: Ord + fmt::Debug,
    {
        let root = self.root.as_ref().map(Borrow::borrow);
        let (red, depth) = (is_red(root), 0);

        if red {
            err_at!(Fatal, msg: "root node must be black")?;
        }

        let n_blacks = 0;
        let (_, n_count) = validate_tree(root, red, n_blacks, depth)?;
        if n_count != self.n_count {
            err_at!(Fatal, msg: "n_count {} != {}", n_count, self.n_count)?;
        }

        Ok(())
    }
}

#[inline]
fn is_red<K, V>(node: Option<&Node<K, V>>) -> bool {
    node.map_or(false, |node| !node.is_black())
}

#[inline]
fn is_black<K, V>(node: Option<&Node<K, V>>) -> bool {
    node.map_or(true, Node::is_black)
}

fn walkuprot_23<K, V>(mut node: Node<K, V>) -> Node<K, V>
where
    K: Clone,
    V: Clone,
{
    if is_red(node.as_right_ref()) && !is_red(node.as_left_ref()) {
        node = rotate_left(node)
    }
    let left = node.as_left_ref();
    if is_red(left) && is_red(left.unwrap().as_left_ref()) {
        node = rotate_right(node);
    }
    if is_red(node.as_left_ref()) && is_red(node.as_right_ref()) {
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
fn rotate_left<K, V>(mut node: Node<K, V>) -> Node<K, V>
where
    K: Clone,
    V: Clone,
{
    let old_right: &Node<K, V> = node.right.as_ref().map(|r| r.borrow()).unwrap();
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
fn rotate_right<K, V>(mut node: Node<K, V>) -> Node<K, V>
where
    K: Clone,
    V: Clone,
{
    let old_left: &Node<K, V> = node.left.as_ref().map(|l| l.borrow()).unwrap();
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
fn flip<K, V>(node: &mut Node<K, V>)
where
    K: Clone,
    V: Clone,
{
    let mut left = {
        let left: &Node<K, V> = node.left.as_ref().map(|l| l.borrow()).unwrap();
        left.clone()
    };
    let mut right = {
        let right: &Node<K, V> = node.right.as_ref().map(|r| r.borrow()).unwrap();
        right.clone()
    };

    node.toggle_link();
    left.toggle_link();
    right.toggle_link();

    node.left = Some(Arc::new(left));
    node.right = Some(Arc::new(right));
}

fn fixup<K, V>(mut node: Node<K, V>) -> Node<K, V>
where
    K: Clone,
    V: Clone,
{
    if is_red(node.as_right_ref()) {
        node = rotate_left(node)
    }

    let left = node.as_left_ref();
    if is_red(left) && is_red(left.unwrap().as_left_ref()) {
        node = rotate_right(node)
    }

    if is_red(node.as_left_ref()) && is_red(node.as_right_ref()) {
        flip(&mut node)
    }
    node
}

fn move_red_left<K, V>(mut node: Node<K, V>) -> Node<K, V>
where
    K: Clone,
    V: Clone,
{
    flip(&mut node);

    if is_red(node.right.as_ref().unwrap().as_left_ref()) {
        let right = node.right.take().unwrap();
        let newr = {
            let rr: &Node<K, V> = right.borrow();
            rr.clone()
        };
        node.right = Some(Arc::new(rotate_right(newr)));
        node = rotate_left(node);
        flip(&mut node);
    }
    node
}

fn move_red_right<K, V>(mut node: Node<K, V>) -> Node<K, V>
where
    K: Clone,
    V: Clone,
{
    flip(&mut node);

    if is_red(node.left.as_ref().unwrap().as_left_ref()) {
        node = rotate_right(node);
        flip(&mut node);
    }
    node
}

// Get the latest version for key.
fn get<K, V, Q>(node: Option<&Node<K, V>>, key: &Q) -> Result<(V, u64)>
where
    K: Clone + Borrow<Q>,
    Q: Ord + ?Sized,
    V: Clone,
{
    match node {
        Some(nref) => match nref.as_key().borrow().cmp(key) {
            Ordering::Less => get(nref.as_right_ref(), key),
            Ordering::Greater => get(nref.as_left_ref(), key),
            Ordering::Equal => {
                let entry: &Entry<V> = nref.entry.as_ref();
                Ok((entry.to_value(), entry.to_seqno()))
            }
        },
        None => err_at!(KeyNotFound, msg: "get missing key"),
    }
}

fn validate_tree<K, V>(
    node: Option<&Node<K, V>>,
    fromred: bool,
    mut n_blacks: usize,
    depth: usize,
) -> Result<(usize, usize)>
where
    K: Ord + fmt::Debug,
{
    let red = is_red(node);

    let node = match node {
        Some(_) if fromred && red => err_at!(Fatal, msg: "OMap has consecutive reds")?,
        Some(node) => node,
        None => return Ok((n_blacks, 0)),
    };

    if !red {
        n_blacks += 1;
    }

    if depth > MAX_TREE_DEPTH {
        err_at!(Fatal, msg: "tree exceeds max_depth {}", depth)?;
    }

    // confirm sort order in the tree.
    let (left, right) = {
        if let Some(left) = node.as_left_ref() {
            if left.as_key().ge(node.as_key()) {
                let (lk, nk) = (left.as_key(), node.as_key());
                err_at!(Fatal, msg: "OMap left:{:?}, parent:{:?}", lk, nk)?;
            }
        }
        if let Some(right) = node.as_right_ref() {
            if right.as_key().le(node.as_key()) {
                let (rk, nk) = (right.as_key(), node.as_key());
                err_at!(Fatal, msg: "OMap right:{:?}, parent:{:?}", rk, nk)?;
            }
        }
        (node.as_left_ref(), node.as_right_ref())
    };

    let (lb, lc) = validate_tree(left, red, n_blacks, depth + 1)?;
    let (rb, rc) = validate_tree(right, red, n_blacks, depth + 1)?;

    if lb != rb {
        err_at!(Fatal, msg: "OMap unbalanced blacks l:{}, r:{}", lb, rb)?;
    }

    Ok((lb, lc + rc + 1))
}

// Iterator type, to do full table scan.
//
// A full table scan using this type is optimal when used with concurrent
// read threads, but not with concurrent write threads.
pub struct Iter<K, V> {
    paths: Vec<Fragment<K, V>>,
    frwrd: bool,
}

impl<K, V> Iterator for Iter<K, V>
where
    K: Clone,
    V: Clone,
{
    type Item = (K, V);

    fn next(&mut self) -> Option<Self::Item> {
        loop {
            let path = self.paths.last_mut()?;
            if self.frwrd {
                match path.flag {
                    IFlag::Left => {
                        path.flag = IFlag::Center;
                        let value = path.node.entry.as_ref().to_value();
                        break Some((path.node.key.clone(), value));
                    }
                    IFlag::Center => {
                        path.flag = IFlag::Right;
                        let right = path.node.right.as_ref().map(Arc::clone);
                        build_iter(IFlag::Left, right, &mut self.paths)
                    }
                    IFlag::Right => {
                        self.paths.pop();
                    }
                }
            } else {
                match path.flag {
                    IFlag::Right => {
                        path.flag = IFlag::Center;
                        let value = path.node.entry.as_ref().to_value();
                        break Some((path.node.key.clone(), value));
                    }
                    IFlag::Center => {
                        path.flag = IFlag::Left;
                        let left = path.node.left.as_ref().map(Arc::clone);
                        build_iter(IFlag::Right, left, &mut self.paths)
                    }
                    IFlag::Left => {
                        self.paths.pop();
                    }
                }
            }
        }
    }
}

// Iterator type, to do range scan between a _lower-bound_ and _higher-bound_.
pub struct Range<K, V, R, Q>
where
    Q: ?Sized,
{
    range: R,
    iter: Iter<K, V>,
    fin: bool,
    high: marker::PhantomData<Q>,
}

impl<K, V, R, Q> Iterator for Range<K, V, R, Q>
where
    K: Clone + Borrow<Q>,
    V: Clone,
    Q: Ord + ?Sized,
    R: RangeBounds<Q>,
{
    type Item = (K, V);

    fn next(&mut self) -> Option<Self::Item> {
        match self.fin {
            false => {
                let (key, value) = self.iter.next()?;
                let qey = key.borrow();
                match self.range.end_bound() {
                    Bound::Unbounded => Some((key, value)),
                    Bound::Included(high) if qey.le(high) => Some((key, value)),
                    Bound::Excluded(high) if qey.lt(high) => Some((key, value)),
                    Bound::Included(_) | Bound::Excluded(_) => {
                        self.fin = true;
                        None
                    }
                }
            }
            true => None,
        }
    }
}

// Iterator type, to do range scan between a _higher-bound_ and _lower-bound_.
pub struct Reverse<K, V, R, Q>
where
    Q: ?Sized,
{
    range: R,
    iter: Iter<K, V>,
    fin: bool,
    low: marker::PhantomData<Q>,
}

impl<K, V, R, Q> Iterator for Reverse<K, V, R, Q>
where
    K: Clone + Borrow<Q>,
    V: Clone,
    R: RangeBounds<Q>,
    Q: Ord + ?Sized,
{
    type Item = (K, V);

    fn next(&mut self) -> Option<Self::Item> {
        match self.fin {
            false => {
                let (key, value) = self.iter.next()?;
                let qey = key.borrow();
                match self.range.start_bound() {
                    Bound::Unbounded => Some((key, value)),
                    Bound::Included(low) if qey.ge(low) => Some((key, value)),
                    Bound::Excluded(low) if qey.gt(low) => Some((key, value)),
                    Bound::Included(_) | Bound::Excluded(_) => {
                        self.fin = true;
                        None
                    }
                }
            }
            true => None,
        }
    }
}

// Continuous iteration without walking through the whole tree from root.
// Achieved by maintaining a FIFO queue of tree-path to the previous
// iterated node. Each node in the FIFO queue is a tuple of mdb-node and
// its current state (IFlag), together this tuple is called as a Fragment.
struct Fragment<K, V> {
    flag: IFlag,
    node: Arc<Node<K, V>>,
}
#[derive(Copy, Clone)]
enum IFlag {
    Left,   // left path is iterated.
    Center, // current node is iterated.
    Right,  // right paths is being iterated.
}

fn build_iter<K, V>(
    flag: IFlag,
    node: Option<Arc<Node<K, V>>>,
    paths: &mut Vec<Fragment<K, V>>,
) {
    if let Some(node) = node {
        let item = Fragment {
            flag,
            node: Arc::clone(&node),
        };
        let node = match flag {
            IFlag::Left => node.left.as_ref().map(Arc::clone),
            IFlag::Right => node.right.as_ref().map(Arc::clone),
            IFlag::Center => unreachable!(),
        };
        paths.push(item);
        build_iter(flag, node, paths)
    }
}

fn find_start<K, V, Q>(
    node: Option<Arc<Node<K, V>>>,
    low: &Q,
    incl: bool,
    paths: &mut Vec<Fragment<K, V>>,
) where
    K: Borrow<Q>,
    Q: Ord + ?Sized,
{
    if let Some(node) = node {
        let left = node.left.as_ref().map(Arc::clone);
        let right = node.right.as_ref().map(Arc::clone);

        let cmp = node.as_key().borrow().cmp(low);

        let flag = match cmp {
            Ordering::Less => IFlag::Right,
            Ordering::Equal if incl => IFlag::Left,
            Ordering::Equal => IFlag::Center,
            Ordering::Greater => IFlag::Left,
        };
        paths.push(Fragment { flag, node });

        match cmp {
            Ordering::Equal => (),
            Ordering::Less => find_start(right, low, incl, paths),
            Ordering::Greater => find_start(left, low, incl, paths),
        }
    }
}

fn find_end<K, V, Q>(
    node: Option<Arc<Node<K, V>>>,
    high: &Q,
    incl: bool,
    paths: &mut Vec<Fragment<K, V>>,
) where
    K: Borrow<Q>,
    Q: Ord + ?Sized,
{
    if let Some(node) = node {
        let left = node.left.as_ref().map(Arc::clone);
        let right = node.right.as_ref().map(Arc::clone);

        let cmp = node.as_key().borrow().cmp(high);

        let flag = match cmp {
            Ordering::Less => IFlag::Right,
            Ordering::Equal if incl => IFlag::Right,
            Ordering::Equal => IFlag::Center,
            Ordering::Greater => IFlag::Left,
        };
        paths.push(Fragment { flag, node });

        match cmp {
            Ordering::Equal => (),
            Ordering::Less => find_end(right, high, incl, paths),
            Ordering::Greater => find_end(left, high, incl, paths),
        }
    }
}

#[cfg(test)]
#[path = "mdb_test.rs"]
mod mdb_test;
