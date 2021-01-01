//! Module provide ordered-map implemented by [OMap] type.
//!
//! OMap is implemented using [left-leaning-red-black][wiki-llrb].
//!
//! - Each entry in OMap instance correspond to a {Key, Value} pair.
//! - Parametrised over `key-type` and `value-type`.
//! - CRUD operations, via create(), set(), get(), delete() api.
//! - Full table scan, to iterate over all entries.
//! - Range scan, to iterate between a ``low`` and ``high``.
//! - Reverse iteration.
//! - No Durability guarantee.
//! - Not thread safe.
//!
//! [OMap] instance and its API uses Rust's ownership model and borrow
//! semantics to ensure thread safe operation.
//!
//! Constructing a new [OMap] instance:
//! ```
//! let index: OMap<i32,i32> = OMap::new("myinstance");
//! let id = index.id();
//! assert_eq!(id, "myinstance");
//! ```
//!
//! CRUD operations on [OMap] instance:
//! ```
//! let mut index: OMap<String,String> = OMap::new("myinstance");
//!
//! index.create("key1".to_string(), "value1".to_string());
//! index.create("key2".to_string(), "value2".to_string());
//! index.set("key2".to_string(), "value3".to_string());
//!
//! let n = index.len();
//! assert_eq!(n, 2);
//!
//! let value = index.get("key1").unwrap();
//! assert_eq!(value, "value1".to_string());
//! let value = index.get("key2").unwrap();
//! assert_eq!(value, "value3".to_string());
//!
//! let old_value = index.delete("key1").unwrap();
//! assert_eq!(old_value, "value1".to_string());
//! ```
//!
//! Full table scan:
//! ```
//! let mut index: OMap<String,String> = OMap::new("myinstance");
//! index.set("key1".to_string(), "value1".to_string());
//! index.set("key2".to_string(), "value2".to_string());
//!
//! for (i, (key, value)) in index.iter().enumerate() {
//!     let refkey = format!("key{}", i+1);
//!     let refval = format!("value{}", i+1);
//!     assert_eq!(refkey, key);
//!     assert_eq!(refval, value);
//! }
//! ```
//!
//! Range scan:
//! ```
//! let mut index: OMap<String,String> = OMap::new("myinstance");
//!
//! index.set("key1".to_string(), "value1".to_string());
//! index.set("key2".to_string(), "value2".to_string());
//! index.set("key3".to_string(), "value3".to_string());
//!
//! let low = Bound::Excluded("key1");
//! let high = Bound::Excluded("key2");
//! let item = index.range::<str, _>((low, high)).next();
//! assert_eq!(item, None);
//!
//! let low = Bound::Excluded("key1");
//! let high = Bound::Excluded("key3");
//! let item = index.range::<str, _>((low, high)).next();
//! assert_eq!(item, Some(("key2".to_string(), "value2".to_string())));
//!
//! let low = Bound::Included("key1");
//! let high = Bound::Included("key3");
//! let mut ranger = index.range::<str, _>((low, high));
//! let item = ranger.next();
//! assert_eq!(item, Some(("key1".to_string(), "value1".to_string())));
//! let item = ranger.last();
//! assert_eq!(item, Some(("key3".to_string(), "value3".to_string())));
//! ```
//!
//! Reverse scan:
//! ```
//! use std::ops::Bound;
//! let mut index: OMap<String,String> = OMap::new("myinstance");
//!
//! index.set("key1".to_string(), "value1".to_string());
//! index.set("key2".to_string(), "value2".to_string());
//! index.set("key3".to_string(), "value3".to_string());
//!
//! let low = Bound::Included("key1");
//! let high = Bound::Included("key3");
//! let mut iter = index.reverse::<_, str>((low, high));
//! let item = iter.next();
//! assert_eq!(item, Some(("key3".to_string(), "value3".to_string())));
//! let item = iter.last();
//! assert_eq!(item, Some(("key1".to_string(), "value1".to_string())));
//! ```
//!
//! [wiki-llrb]: https://en.wikipedia.org/wiki/Left-leaning_red-black_tree

use rand::Rng;

use std::{
    borrow::Borrow,
    cmp::{Ord, Ordering},
    fmt, marker,
    ops::{Bound, Deref, DerefMut, RangeBounds},
};

use crate::{Error, Result};

/// OMap manage a single instance of in-memory ordered-map using
/// [left-leaning-red-black][llrb] tree.
///
/// [llrb]: https://en.wikipedia.org/wiki/Left-leaning_red-black_tree
pub struct OMap<K, V> {
    root: Option<Box<Node<K, V>>>,
    n_count: usize, // number of entries in the tree.
}

//impl<K, V> Extend<(K, V)> for OMap<K, V>
//where
//    K: Ord,
//{
//    fn extend<I>(&mut self, iter: I)
//    where
//        I: IntoIterator<Item = (K, V)>,
//    {
//        iter.into_iter().for_each(|(key, value)| {
//            self.set(key, value);
//        });
//    }
//}

impl<K, V> OMap<K, V> {
    /// Create an empty instance of OMap.
    pub fn new() -> OMap<K, V> {
        OMap {
            root: None,
            n_count: Default::default(),
        }
    }
}

/// Maintenance API.
impl<K, V> OMap<K, V> {
    /// Return number of entries in this instance.
    #[inline]
    pub fn len(&self) -> usize {
        self.n_count
    }

    /// Check whether this index is empty.
    #[inline]
    pub fn is_empty(&self) -> bool {
        self.n_count == 0
    }
}

impl<K, V> OMap<K, V> {
    /// Set value for key. If there is an existing entry for key,
    /// overwrite the old value with new value and return the old value.
    pub fn set(&mut self, key: K, value: V) -> Option<V>
    where
        K: Ord,
        V: Clone,
    {
        let (mut root, old_value) = Self::do_set(self.root.take(), key, value);
        root.set_black();
        self.root = Some(root);
        if old_value.is_none() {
            self.n_count += 1;
        }
        old_value
    }

    /// Delete key from this instance and return its value. If key is
    /// not present, then delete is effectively a no-op.
    pub fn delete<Q>(&mut self, key: &Q) -> Option<V>
    where
        K: Clone + Borrow<Q>,
        V: Clone,
        Q: Ord + ?Sized,
    {
        let (root, old_value) = match Self::do_delete(self.root.take(), key) {
            (None, old_value) => (None, old_value),
            (Some(mut root), old_value) => {
                root.set_black();
                (Some(root), old_value)
            }
        };
        self.root = root;
        if old_value.is_some() {
            self.n_count -= 1;
        }
        old_value
    }

    /// Validate LLRB tree with following rules:
    ///
    /// * From root to any leaf, no consecutive reds allowed in its path.
    /// * Number of blacks should be same under left child and right child.
    /// * Make sure keys are in sorted order.
    ///
    /// Additionally return full statistics on the tree. Refer to [`Stats`]
    /// for more information.
    pub fn validate(&self) -> Result<()>
    where
        K: Ord + fmt::Debug,
    {
        let root = self.root.as_ref().map(Deref::deref);
        Self::validate_tree(root, is_red(root), 0 /*n_blacks*/, 1 /*depth*/)?;
        Ok(())
    }
}

impl<K, V> OMap<K, V> {
    /// Get the value for key.
    pub fn get<Q>(&self, key: &Q) -> Option<V>
    where
        K: Borrow<Q>,
        V: Clone,
        Q: Ord + ?Sized,
    {
        let mut node = self.root.as_ref().map(Deref::deref);
        while let Some(nref) = node {
            node = match nref.key.borrow().cmp(key) {
                Ordering::Less => nref.as_right_ref(),
                Ordering::Greater => nref.as_left_ref(),
                Ordering::Equal => return Some(nref.value.clone()),
            };
        }
        None
    }

    /// Return an iterator over all entries in this instance.
    pub fn iter(&self) -> Iter<K, V> {
        let node = self.root.as_ref().map(Deref::deref);

        let mut paths = Vec::default();
        build_iter(IFlag::Left, node, &mut paths);

        Iter { paths }
    }

    /// Range over all entries from low to high.
    pub fn range<Q, R>(&self, range: R) -> Range<K, V, R, Q>
    where
        K: Borrow<Q>,
        R: RangeBounds<Q>,
        Q: Ord + ?Sized,
    {
        let root = self.root.as_ref().map(Deref::deref);

        let mut paths = Vec::default();
        match range.start_bound() {
            Bound::Unbounded => build_iter(IFlag::Left, root, &mut paths),
            Bound::Included(low) => find_start(root, low, true, &mut paths),
            Bound::Excluded(low) => find_start(root, low, false, &mut paths),
        };
        let iter = Iter { paths };

        Range {
            range,
            iter,
            fin: false,
            high: marker::PhantomData,
        }
    }

    /// Reverse range over all entries from high to low.
    pub fn reverse<R, Q>(&self, range: R) -> Reverse<K, V, R, Q>
    where
        K: Borrow<Q>,
        R: RangeBounds<Q>,
        Q: Ord + ?Sized,
    {
        let root = self.root.as_ref().map(Deref::deref);

        let mut paths = Vec::default();
        match range.end_bound() {
            Bound::Unbounded => build_iter(IFlag::Right, root, &mut paths),
            Bound::Included(high) => find_end(root, high, true, &mut paths),
            Bound::Excluded(high) => find_end(root, high, false, &mut paths),
        };
        let iter = Iter { paths };

        Reverse {
            range,
            iter,
            fin: false,
            low: marker::PhantomData,
        }
    }

    /// Return a random entry from this index.
    pub fn random<R: Rng>(&self, rng: &mut R) -> Option<(K, V)>
    where
        K: Clone,
        V: Clone,
    {
        let mut nref = self.root.as_ref().map(Deref::deref)?;

        let mut at_depth = rng.gen::<u8>() % 40;

        loop {
            let next = match rng.gen::<u8>() % 2 {
                0 => nref.as_left_ref(),
                1 => nref.as_right_ref(),
                _ => unreachable!(),
            };

            if at_depth == 0 || next.is_none() {
                break Some((nref.key.clone(), nref.value.clone()));
            }
            at_depth -= 1;
            nref = next.unwrap();
        }
    }
}

type Upsert<K, V> = (Box<Node<K, V>>, Option<V>);
type Delete<K, V> = (Option<Box<Node<K, V>>>, Option<V>);
type Delmin<K, V> = (Option<Box<Node<K, V>>>, Option<Node<K, V>>);

impl<K, V> OMap<K, V> {
    fn do_set(node: Option<Box<Node<K, V>>>, key: K, value: V) -> Upsert<K, V>
    where
        K: Ord,
        V: Clone,
    {
        let mut node = match node {
            Some(node) => node,
            None => return (Box::new(Node::new(key, value, false /*black*/)), None),
        };

        match node.key.cmp(&key) {
            Ordering::Greater => {
                let (left, o) = Self::do_set(node.left.take(), key, value);
                node.left = Some(left);
                (walkuprot_23(node), o)
            }
            Ordering::Less => {
                let (right, o) = Self::do_set(node.right.take(), key, value);
                node.right = Some(right);
                (walkuprot_23(node), o)
            }
            Ordering::Equal => {
                let old_value = node.value.clone();
                node.set_value(value);
                (walkuprot_23(node), Some(old_value))
            }
        }
    }

    fn do_delete<Q>(node: Option<Box<Node<K, V>>>, key: &Q) -> Delete<K, V>
    where
        K: Clone + Borrow<Q>,
        V: Clone,
        Q: Ord + ?Sized,
    {
        let mut node = match node {
            None => return (None, None),
            Some(node) => node,
        };

        if node.key.borrow().gt(key) {
            if node.left.is_none() {
                (Some(node), None)
            } else {
                let ok = !is_red(node.as_left_ref());
                if ok && !is_red(node.left.as_ref().unwrap().as_left_ref()) {
                    node = move_red_left(node);
                }
                let (left, old_value) = Self::do_delete(node.left.take(), key);
                node.left = left;
                (Some(fixup(node)), old_value)
            }
        } else {
            if is_red(node.as_left_ref()) {
                node = rotate_right(node);
            }

            if !node.key.borrow().lt(key) && node.right.is_none() {
                return (None, Some(node.value.clone()));
            }

            let ok = node.right.is_some() && !is_red(node.as_right_ref());
            if ok && !is_red(node.right.as_ref().unwrap().as_left_ref()) {
                node = move_red_right(node);
            }

            if !node.key.borrow().lt(key) {
                // node == key
                let (right, mut res_node) = Self::delete_min(node.right.take());
                node.right = right;
                if res_node.is_none() {
                    panic!("do_delete(): fatal logic, call the programmer");
                }
                let subdel = res_node.take().unwrap();
                let mut newnode = Box::new(subdel.clone_detach());
                newnode.left = node.left.take();
                newnode.right = node.right.take();
                newnode.black = node.black;
                (Some(fixup(newnode)), Some(node.value.clone()))
            } else {
                let (right, old_value) = Self::do_delete(node.right.take(), key);
                node.right = right;
                (Some(fixup(node)), old_value)
            }
        }
    }

    fn delete_min(node: Option<Box<Node<K, V>>>) -> Delmin<K, V> {
        if node.is_none() {
            return (None, None);
        }
        let mut node = node.unwrap();
        if node.left.is_none() {
            return (None, Some(*node));
        }
        let left = node.as_left_ref();
        if !is_red(left) && !is_red(left.unwrap().as_left_ref()) {
            node = move_red_left(node);
        }
        let (left, old_node) = Self::delete_min(node.left.take());
        node.left = left;
        (Some(fixup(node)), old_node)
    }

    fn validate_tree(
        node: Option<&Node<K, V>>,
        fromred: bool,
        mut n_blacks: usize,
        depth: usize,
    ) -> Result<usize>
    where
        K: Ord + fmt::Debug,
    {
        let node = match node {
            Some(node) => node,
            None => return Ok(n_blacks),
        };

        let red = is_red(Some(node));
        if fromred && red {
            return err_at!(Fatal, msg: "consecutive reds")?;
        }

        if !red {
            n_blacks += 1;
        }

        let (left, right) = (node.as_left_ref(), node.as_right_ref());
        let lblacks = Self::validate_tree(left, red, n_blacks, depth + 1)?;
        let rblacks = Self::validate_tree(right, red, n_blacks, depth + 1)?;
        if lblacks != rblacks {
            err_at!(Fatal, msg: "unbalanced blacks {} {}", lblacks, rblacks)?;
        }

        if let Some(left) = left {
            if left.key.ge(&node.key) {
                err_at!(Fatal, msg: "sort lkey:{:?} parent:{:?}", left.key, node.key)?;
            }
        }
        if let Some(right) = right {
            if right.key.le(&node.key) {
                err_at!(Fatal, msg: "sort lkey:{:?} parent:{:?}", right.key, node.key)?;
            }
        }

        Ok(lblacks)
    }
}

fn is_red<K, V>(node: Option<&Node<K, V>>) -> bool {
    node.map_or(false, |node| !node.is_black())
}

fn is_black<K, V>(node: Option<&Node<K, V>>) -> bool {
    node.map_or(true, |node| node.is_black())
}

//--------- rotation routines for 2-3 algorithm ----------------

fn walkuprot_23<K, V>(mut node: Box<Node<K, V>>) -> Box<Node<K, V>> {
    if is_red(node.as_right_ref()) && !is_red(node.as_left_ref()) {
        node = rotate_left(node);
    }
    let left = node.as_left_ref();
    if is_red(left) && is_red(left.unwrap().as_left_ref()) {
        node = rotate_right(node);
    }
    if is_red(node.as_left_ref()) && is_red(node.as_right_ref()) {
        flip(node.deref_mut())
    }
    node
}

//              (i)                       (i)
//               |                         |
//              node                       x
//              /  \                      / \
//             /    (r)                 (r)  \
//            /       \                 /     \
//          left       x             node      xr
//                    / \            /  \
//                  xl   xr       left   xl
//
fn rotate_left<K, V>(mut node: Box<Node<K, V>>) -> Box<Node<K, V>> {
    if is_black(node.as_right_ref()) {
        panic!("rotateleft(): rotating a black link ? Call the programmer");
    }
    let mut x = node.right.take().unwrap();
    node.right = x.left.take();
    x.black = node.black;
    node.set_red();
    x.left = Some(node);
    x
}

//              (i)                       (i)
//               |                         |
//              node                       x
//              /  \                      / \
//            (r)   \                   (r)  \
//           /       \                 /      \
//          x       right             xl      node
//         / \                                / \
//       xl   xr                             xr  right
//
fn rotate_right<K, V>(mut node: Box<Node<K, V>>) -> Box<Node<K, V>> {
    if is_black(node.as_left_ref()) {
        panic!("rotateright(): rotating a black link ? Call the programmer")
    }
    let mut x = node.left.take().unwrap();
    node.left = x.right.take();
    x.black = node.black;
    node.set_red();
    x.right = Some(node);
    x
}

//        (x)                   (!x)
//         |                     |
//        node                  node
//        / \                   / \
//      (y) (z)              (!y) (!z)
//     /      \              /      \
//   left    right         left    right
//
fn flip<K, V>(node: &mut Node<K, V>) {
    if let Some(left) = node.left.as_mut() {
        left.toggle_link();
    }
    if let Some(right) = node.right.as_mut() {
        right.toggle_link();
    }
    node.toggle_link();
}

fn fixup<K, V>(mut node: Box<Node<K, V>>) -> Box<Node<K, V>> {
    if is_red(node.as_right_ref()) {
        node = rotate_left(node);
    }

    let left = node.as_left_ref();
    if is_red(left) && is_red(left.unwrap().as_left_ref()) {
        node = rotate_right(node);
    }

    if is_red(node.as_left_ref()) && is_red(node.as_right_ref()) {
        flip(node.deref_mut());
    }
    node
}

fn move_red_left<K, V>(mut node: Box<Node<K, V>>) -> Box<Node<K, V>> {
    flip(node.deref_mut());
    if is_red(node.right.as_ref().unwrap().as_left_ref()) {
        node.right = Some(rotate_right(node.right.take().unwrap()));
        node = rotate_left(node);
        flip(node.deref_mut());
    }
    node
}

fn move_red_right<K, V>(mut node: Box<Node<K, V>>) -> Box<Node<K, V>> {
    flip(node.deref_mut());
    if is_red(node.left.as_ref().unwrap().as_left_ref()) {
        node = rotate_right(node);
        flip(node.deref_mut());
    }
    node
}

pub struct Iter<'a, K, V> {
    paths: Vec<Fragment<'a, K, V>>,
}

impl<'a, K, V> Iterator for Iter<'a, K, V>
where
    K: Clone,
    V: Clone,
{
    type Item = (K, V);

    fn next(&mut self) -> Option<Self::Item> {
        loop {
            let path = self.paths.last_mut()?;
            match path.flag {
                IFlag::Left => {
                    path.flag = IFlag::Center;
                    break Some((path.node.key.clone(), path.node.value.clone()));
                }
                IFlag::Center => {
                    path.flag = IFlag::Right;
                    let right = path.node.right.as_ref().map(AsRef::as_ref);
                    build_iter(IFlag::Left, right, &mut self.paths)
                }
                IFlag::Right => {
                    self.paths.pop();
                }
            }
        }
    }
}

pub struct Range<'a, K, V, R, Q>
where
    Q: ?Sized,
{
    range: R,
    iter: Iter<'a, K, V>,
    fin: bool,
    high: marker::PhantomData<Q>,
}

impl<'a, K, V, R, Q> Iterator for Range<'a, K, V, R, Q>
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
                let (key, val) = self.iter.next()?;
                match self.range.end_bound() {
                    Bound::Included(high) if key.borrow().le(high) => Some((key, val)),
                    Bound::Excluded(high) if key.borrow().lt(high) => Some((key, val)),
                    Bound::Unbounded => Some((key, val)),
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

pub struct Reverse<'a, K, V, R, Q>
where
    Q: ?Sized,
{
    range: R,
    iter: Iter<'a, K, V>,
    fin: bool,
    low: marker::PhantomData<Q>,
}

impl<'a, K, V, R, Q> Iterator for Reverse<'a, K, V, R, Q>
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
                let (key, val) = self.iter.next()?;
                match self.range.start_bound() {
                    Bound::Included(low) if key.borrow().ge(low) => Some((key, val)),
                    Bound::Excluded(low) if key.borrow().gt(low) => Some((key, val)),
                    Bound::Unbounded => Some((key, val)),
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

/// Node corresponds to a single entry in Llrb instance.
#[derive(Clone)]
pub struct Node<K, V> {
    key: K,
    value: V,
    black: bool,                    // store: black or red
    left: Option<Box<Node<K, V>>>,  // store: left child
    right: Option<Box<Node<K, V>>>, // store: right child
}

impl<K, V> Node<K, V> {
    fn new(key: K, value: V, black: bool) -> Node<K, V> {
        Node {
            key,
            value,
            black,
            left: None,
            right: None,
        }
    }

    fn clone_detach(&self) -> Node<K, V>
    where
        K: Clone,
        V: Clone,
    {
        Node {
            key: self.key.clone(),
            value: self.value.clone(),
            black: self.black,
            left: None,
            right: None,
        }
    }

    #[inline]
    fn as_left_ref(&self) -> Option<&Node<K, V>> {
        self.left.as_ref().map(AsRef::as_ref)
    }

    #[inline]
    fn as_right_ref(&self) -> Option<&Node<K, V>> {
        self.right.as_ref().map(AsRef::as_ref)
    }

    #[inline]
    fn set_value(&mut self, value: V) {
        self.value = value
    }

    #[inline]
    fn set_red(&mut self) {
        self.black = false
    }

    #[inline]
    fn set_black(&mut self) {
        self.black = true
    }

    #[inline]
    fn toggle_link(&mut self) {
        self.black = !self.black
    }

    #[inline]
    fn is_black(&self) -> bool {
        self.black
    }
}

#[derive(Copy, Clone)]
enum IFlag {
    Left,
    Center,
    Right,
}

struct Fragment<'a, K, V> {
    flag: IFlag,
    node: &'a Node<K, V>,
}

fn build_iter<'a, K, V>(
    flag: IFlag,
    node: Option<&'a Node<K, V>>,
    paths: &mut Vec<Fragment<'a, K, V>>,
) {
    if let Some(node) = node {
        let item = Fragment { flag, node };
        let node = match flag {
            IFlag::Left => item.node.left.as_ref().map(AsRef::as_ref),
            IFlag::Right => item.node.right.as_ref().map(AsRef::as_ref),
            IFlag::Center => unreachable!(),
        };
        paths.push(item);
        build_iter(flag, node, paths)
    }
}

fn find_start<'a, K, V, Q>(
    node: Option<&'a Node<K, V>>,
    low: &Q,
    incl: bool,
    paths: &mut Vec<Fragment<'a, K, V>>,
) where
    K: Borrow<Q>,
    Q: Ord + ?Sized,
{
    if let Some(node) = node {
        let left = node.left.as_ref().map(AsRef::as_ref);
        let right = node.right.as_ref().map(AsRef::as_ref);

        let cmp = node.key.borrow().cmp(low);

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

fn find_end<'a, K, V, Q>(
    node: Option<&'a Node<K, V>>,
    high: &Q,
    incl: bool,
    paths: &mut Vec<Fragment<'a, K, V>>,
) where
    K: Borrow<Q>,
    Q: Ord + ?Sized,
{
    if let Some(node) = node {
        let left = node.left.as_ref().map(AsRef::as_ref);
        let right = node.right.as_ref().map(AsRef::as_ref);

        let cmp = node.key.borrow().cmp(high);

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

//#[cfg(test)]
//#[path = "llrb_test.rs"]
//mod llrb_test;
