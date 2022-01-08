use std::{
    borrow::Borrow,
    cmp::{Ord, Ordering},
    fmt, marker,
    ops::{Bound, RangeBounds},
};

use super::*;
use crate::{Error, Result};

// IMPORTANT: ppom::OMap type does not use Node from node module, instead it
// implements its own Node in this module.

/// Fully Persistent array using [Left-leaning-red-black][llrb] tree.
///
/// Refer package level documentation for brief description.
///
/// [llrb]: https://en.wikipedia.org/wiki/Left-leaning_red-black_tree
#[derive(Clone, Default)]
pub struct OMap<K, V> {
    root: Option<Ref<Node<K, V>>>,
    n_count: usize, // number of entries in the tree.
}

impl<K, V> OMap<K, V> {
    pub fn new() -> OMap<K, V> {
        OMap {
            root: None,
            n_count: Default::default(),
        }
    }
}

impl<K, V> OMap<K, V> {
    /// Return number of entries in index.
    #[inline]
    pub fn len(&self) -> usize {
        self.n_count
    }

    /// Check whether this index is empty.
    #[inline]
    pub fn is_empty(&self) -> bool {
        self.n_count == 0
    }

    #[allow(dead_code)]
    #[cfg(test)]
    pub fn pretty_print(&self)
    where
        K: fmt::Debug,
        V: fmt::Debug,
    {
        if let Some(n) = self.root.as_ref() {
            n.as_ref().pretty_print("".to_string())
        }
    }
}

impl<K, V> OMap<K, V> {
    /// Set value for key. If there is an existing entry for key,
    /// overwrite the old value with new value and return the old value.
    pub fn set(&self, key: K, value: V) -> Self
    where
        K: Ord + Clone,
        V: Clone,
    {
        let root = self.root.as_deref();
        let (mut root, is_old) = Self::do_set(root, key, value);

        root.set_black();

        OMap {
            root: Some(Ref::new(root)),
            n_count: if is_old {
                self.n_count
            } else {
                self.n_count + 1
            },
        }
    }

    /// Remove key from this instance and return its value. If key is
    /// not present, then delete is effectively a no-op.
    pub fn remove<Q>(&self, key: &Q) -> Self
    where
        K: Clone + Borrow<Q>,
        V: Clone,
        Q: Ord + ?Sized,
    {
        let root = self.root.as_deref();
        let (root, is_old) = match Self::do_remove(root, key) {
            (None, is_old) => (None, is_old),
            (Some(mut root), is_old) => {
                root.set_black();
                (Some(Ref::new(root)), is_old)
            }
        };

        OMap {
            root,
            n_count: if is_old {
                self.n_count - 1
            } else {
                self.n_count
            },
        }
    }

    /// Validate tree with following rules:
    ///
    /// * From root to any leaf, no consecutive reds allowed in its path.
    /// * Number of blacks should be same under left child and right child.
    /// * Make sure keys are in sorted order.
    pub fn validate(&self) -> Result<()>
    where
        K: Ord + fmt::Debug,
    {
        let root = self.root.as_deref();
        let (n_count, n_blacks, depth) = (0, 0, 1);
        let (n_count, _) =
            Self::validate_tree(root, is_red(root), n_count, n_blacks, depth)?;
        if n_count != self.n_count {
            err_at!(Fatal, msg: "mismatch in count {} != {}", n_count, self.n_count)?;
        }
        Ok(())
    }
}

impl<K, V> OMap<K, V> {
    /// Get value for key.
    pub fn get<Q>(&self, key: &Q) -> Option<V>
    where
        K: Borrow<Q>,
        V: Clone,
        Q: Ord + ?Sized,
    {
        let mut node = self.root.as_deref();
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
    ///
    /// ```
    /// use ppom::OMap;
    ///
    /// let mut index: OMap<String,String> = OMap::new();
    /// index.set("key1".to_string(), "value1".to_string());
    /// index.set("key2".to_string(), "value2".to_string());
    ///
    /// for (i, (key, value)) in index.iter().enumerate() {
    ///     let refkey = format!("key{}", i+1);
    ///     let refval = format!("value{}", i+1);
    ///     assert_eq!(refkey, key);
    ///     assert_eq!(refval, value);
    /// }
    /// ```
    pub fn iter(&self) -> Iter<K, V> {
        let node = self.root.as_deref();

        let mut paths = Vec::default();
        build_iter(IFlag::Left, node, &mut paths);

        Iter { paths, frwrd: true }
    }

    /// Range over all entries from low to high, specified by `range`.
    ///
    /// ```
    /// use std::ops::Bound;
    /// use ppom::OMap;
    ///
    /// let mut index: OMap<String,String> = OMap::new();
    ///
    /// index.set("key1".to_string(), "value1".to_string());
    /// index.set("key2".to_string(), "value2".to_string());
    /// index.set("key3".to_string(), "value3".to_string());
    ///
    /// let low = Bound::Excluded("key1");
    /// let high = Bound::Excluded("key2");
    /// let item = index.range::<str, _>((low, high)).next();
    /// assert_eq!(item, None);
    ///
    /// let low = Bound::Excluded("key1");
    /// let high = Bound::Excluded("key3");
    /// let item = index.range::<str, _>((low, high)).next();
    /// assert_eq!(item, Some(("key2".to_string(), "value2".to_string())));
    ///
    /// let low = Bound::Included("key1");
    /// let high = Bound::Included("key3");
    /// let mut ranger = index.range::<str, _>((low, high));
    /// let item = ranger.next();
    /// assert_eq!(item, Some(("key1".to_string(), "value1".to_string())));
    /// let item = ranger.last();
    /// assert_eq!(item, Some(("key3".to_string(), "value3".to_string())));
    /// ```
    pub fn range<Q, R>(&self, range: R) -> Range<K, V, R, Q>
    where
        K: Borrow<Q>,
        R: RangeBounds<Q>,
        Q: Ord + ?Sized,
    {
        let root = self.root.as_deref();

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

    /// Reverse range over all entries from high to low, specified by `range`.
    ///
    /// ```
    /// use std::ops::Bound;
    /// use ppom::OMap;
    ///
    /// let mut index: OMap<String,String> = OMap::new();
    ///
    /// index.set("key1".to_string(), "value1".to_string());
    /// index.set("key2".to_string(), "value2".to_string());
    /// index.set("key3".to_string(), "value3".to_string());
    ///
    /// let low = Bound::Included("key1");
    /// let high = Bound::Included("key3");
    /// let mut iter = index.reverse::<_, str>((low, high));
    ///
    /// let item = iter.next();
    /// assert_eq!(item, Some(("key3".to_string(), "value3".to_string())));
    /// let item = iter.last();
    /// assert_eq!(item, Some(("key1".to_string(), "value1".to_string())));
    /// ```
    pub fn reverse<R, Q>(&self, range: R) -> Reverse<K, V, R, Q>
    where
        K: Borrow<Q>,
        R: RangeBounds<Q>,
        Q: Ord + ?Sized,
    {
        let root = self.root.as_deref();

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

    /// Return a random entry from this index.
    pub fn random<R>(&self, rng: &mut R) -> Option<(K, V)>
    where
        K: Clone,
        V: Clone,
        R: rand::Rng,
    {
        let mut nref = self.root.as_deref()?;

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

type Remmin<K, V> = [Option<Node<K, V>>; 2];

impl<K, V> OMap<K, V> {
    fn do_set(node: Option<&Node<K, V>>, key: K, value: V) -> (Node<K, V>, bool)
    where
        K: Ord + Clone,
        V: Clone,
    {
        let mut node = match node {
            Some(node) => node.clone(),
            None => return (Node::new(key, value, false /*black*/), false),
        };

        match node.key.cmp(&key) {
            Ordering::Greater => {
                let (left, is_old) = Self::do_set(node.as_left_ref(), key, value);
                node.left = Some(Ref::new(left));
                (walkuprot_23(node), is_old)
            }
            Ordering::Less => {
                let (right, is_old) = Self::do_set(node.as_right_ref(), key, value);
                node.right = Some(Ref::new(right));
                (walkuprot_23(node), is_old)
            }
            Ordering::Equal => {
                node.set_value(value);
                (walkuprot_23(node), true)
            }
        }
    }

    fn do_remove<Q>(node: Option<&Node<K, V>>, key: &Q) -> (Option<Node<K, V>>, bool)
    where
        K: Clone + Borrow<Q>,
        V: Clone,
        Q: Ord + ?Sized,
    {
        let mut node = match node {
            Some(node) => node.clone(),
            None => return (None, false),
        };

        match node.key.borrow().cmp(key) {
            Ordering::Greater if node.left.is_none() => (Some(node), false),
            Ordering::Greater => {
                let ok = !is_red(node.as_left_ref());
                if ok && !is_red(node.left.as_ref().unwrap().as_left_ref()) {
                    node = move_red_left(node);
                }
                let (left, is_old) = Self::do_remove(node.as_left_ref(), key);
                node.left = left.map(Ref::new);
                (Some(fixup(node)), is_old)
            }
            _ => {
                if is_red(node.as_left_ref()) {
                    node = rotate_right(node);
                }
                if !node.key.borrow().lt(key) && node.right.is_none() {
                    (None, true)
                } else {
                    node = match node.as_right_ref() {
                        r @ Some(_)
                            if !is_red(r) && !is_red(r.unwrap().as_left_ref()) =>
                        {
                            move_red_right(node)
                        }
                        Some(_) | None => node,
                    };

                    if !node.key.borrow().lt(key) {
                        let [right, sub_node] = Self::remove_min(node.as_right_ref());
                        node.right = right.map(Ref::new);
                        let mut sub_node = match sub_node {
                            Some(sub_node) => sub_node,
                            None => panic!("do_remove(): fatal call the programmer"),
                        };
                        sub_node.left = node.left;
                        sub_node.right = node.right;
                        sub_node.black = node.black;
                        (Some(fixup(sub_node)), true)
                    } else {
                        let (right, is_old) = Self::do_remove(node.as_right_ref(), key);
                        node.right = right.map(Ref::new);
                        (Some(fixup(node)), is_old)
                    }
                }
            }
        }
    }

    fn remove_min(node: Option<&Node<K, V>>) -> Remmin<K, V>
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

        let [left, old_node] = Self::remove_min(node.as_left_ref());
        node.left = left.map(Ref::new);
        [Some(fixup(node)), old_node]
    }

    fn validate_tree(
        node: Option<&Node<K, V>>,
        fromred: bool,
        mut n_count: usize,
        mut n_blacks: usize,
        depth: usize,
    ) -> Result<(usize, usize)>
    where
        K: Ord + fmt::Debug,
    {
        let node = match node {
            Some(node) => node,
            None => return Ok((n_count, n_blacks)),
        };
        n_count += 1;

        let red = is_red(Some(node));
        if fromred && red {
            return err_at!(Fatal, msg: "consecutive reds")?;
        }

        if !red {
            n_blacks += 1;
        }

        let (left, rigt) = (node.as_left_ref(), node.as_right_ref());
        let (n_count, lb) = Self::validate_tree(left, red, n_count, n_blacks, depth + 1)?;
        let (n_count, rb) = Self::validate_tree(rigt, red, n_count, n_blacks, depth + 1)?;
        if lb != rb {
            err_at!(Fatal, msg: "unbalanced blacks {} {}", lb, rb)?;
        }

        if let Some(left) = left {
            if left.key.ge(&node.key) {
                err_at!(Fatal, msg: "sort lkey:{:?} parent:{:?}", left.key, node.key)?;
            }
        }
        if let Some(rigt) = rigt {
            if rigt.key.le(&node.key) {
                err_at!(Fatal, msg: "sort lkey:{:?} parent:{:?}", rigt.key, node.key)?;
            }
        }

        Ok((n_count, lb))
    }
}

fn is_red<K, V>(node: Option<&Node<K, V>>) -> bool {
    node.map_or(false, |node| !node.is_black())
}

fn is_black<K, V>(node: Option<&Node<K, V>>) -> bool {
    node.map_or(true, |node| node.is_black())
}

//--------- rotation routines for 2-3 algorithm ----------------

fn walkuprot_23<K, V>(mut node: Node<K, V>) -> Node<K, V>
where
    K: Clone,
    V: Clone,
{
    if is_red(node.as_right_ref()) && !is_red(node.as_left_ref()) {
        node = rotate_left(node);
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
//              node                       x
//              /  \                      / \
//             /    (r)                 (r)  \
//            /       \                 /     \
//          left       x             node      xr
//                    / \            /  \
//                  xl   xr       left   xl
//
fn rotate_left<K, V>(mut node: Node<K, V>) -> Node<K, V>
where
    K: Clone,
    V: Clone,
{
    let old_right: &Node<K, V> = node.right.as_deref().unwrap();
    if is_black(Some(old_right)) {
        panic!("rotateleft(): rotating a black link ? Call the programmer");
    }

    let mut right = old_right.clone();

    node.right = right.left.take();
    right.black = node.black;
    node.set_red();
    right.left = Some(Ref::new(node));

    right
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
fn rotate_right<K, V>(mut node: Node<K, V>) -> Node<K, V>
where
    K: Clone,
    V: Clone,
{
    let old_left: &Node<K, V> = node.left.as_deref().unwrap();
    if is_black(Some(old_left)) {
        panic!("rotateright(): rotating a black link ? Call the programmer")
    }

    let mut left = old_left.clone();

    node.left = left.right.take();
    left.black = node.black;
    node.set_red();
    left.right = Some(Ref::new(node));

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
        let left: &Node<K, V> = node.left.as_deref().unwrap();
        left.clone()
    };
    let mut right = {
        let right: &Node<K, V> = node.right.as_deref().unwrap();
        right.clone()
    };

    node.toggle_link();
    left.toggle_link();
    right.toggle_link();

    node.left = Some(Ref::new(left));
    node.right = Some(Ref::new(right));
}

fn fixup<K, V>(mut node: Node<K, V>) -> Node<K, V>
where
    K: Clone,
    V: Clone,
{
    if is_red(node.as_right_ref()) {
        node = rotate_left(node);
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
        node.right = Some(Ref::new(rotate_right(newr)));
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

#[derive(Debug)]
pub struct Iter<'a, K, V> {
    paths: Vec<Fragment<'a, K, V>>,
    frwrd: bool,
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
            if self.frwrd {
                match path.flag {
                    IFlag::Left => {
                        path.flag = IFlag::Center;
                        break Some((path.node.key.clone(), path.node.value.clone()));
                    }
                    IFlag::Center => {
                        path.flag = IFlag::Right;
                        let right = path.node.right.as_deref();
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
                        break Some((path.node.key.clone(), path.node.value.clone()));
                    }
                    IFlag::Center => {
                        path.flag = IFlag::Left;
                        let left = path.node.left.as_deref();
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

#[derive(Debug)]
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

#[derive(Debug)]
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

/// Node corresponds to a single entry in tree.
#[derive(Clone, Debug)]
pub struct Node<K, V> {
    key: K,
    value: V,
    black: bool,                    // store: black or red
    left: Option<Ref<Node<K, V>>>,  // store: left child
    right: Option<Ref<Node<K, V>>>, // store: right child
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

    #[inline]
    fn as_left_ref(&self) -> Option<&Node<K, V>> {
        self.left.as_deref()
    }

    #[inline]
    fn as_right_ref(&self) -> Option<&Node<K, V>> {
        self.right.as_deref()
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

    #[allow(dead_code)]
    #[cfg(test)]
    fn pretty_print(&self, mut prefix: String)
    where
        K: fmt::Debug,
        V: fmt::Debug,
    {
        match self.black {
            true => println!("{}(b)<{:?},{:?}>", prefix, self.key, self.value),
            false => println!("{}(r)<{:?},{:?}>", prefix, self.key, self.value),
        }
        prefix.push_str("  ");
        if let Some(l) = self.left.as_ref() {
            l.pretty_print(prefix.clone())
        }
        if let Some(r) = self.right.as_ref() {
            r.pretty_print(prefix)
        }
    }
}

#[derive(Copy, Clone, Debug)]
enum IFlag {
    Left,
    Center,
    Right,
}

#[derive(Debug)]
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
            IFlag::Left => item.node.left.as_deref(),
            IFlag::Right => item.node.right.as_deref(),
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
        let left = node.left.as_deref();
        let right = node.right.as_deref();

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
        let left = node.left.as_deref();
        let right = node.right.as_deref();

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
