use std::{ops::Deref, sync::Arc};

use mkit::{data::Diff, db};

// Node corresponds to a single entry in Llrb instance.
#[derive(Clone)]
pub struct Node<K, V, D> {
    pub entry: Arc<db::Entry<K, V, D>>,
    pub black: bool,                       // store: black or red
    pub left: Option<Arc<Node<K, V, D>>>,  // store: left child
    pub right: Option<Arc<Node<K, V, D>>>, // store: right child
}

impl<K, V, D> Node<K, V, D> {
    pub fn set(&mut self, value: V, seqno: u64)
    where
        K: Clone,
        V: Clone,
        D: Clone,
    {
        let mut entry = self.entry.as_ref().clone();
        entry.value.set(value, seqno);
        self.entry = Arc::new(entry);
    }

    pub fn insert(&mut self, value: V, seqno: u64)
    where
        K: Clone,
        V: Clone + Diff<Delta = D>,
        D: Clone,
    {
        let mut entry = self.entry.as_ref().clone();
        entry.insert(value, seqno);
        self.entry = Arc::new(entry);
    }

    pub fn delete(&mut self, seqno: u64)
    where
        K: Clone,
        V: Clone + Diff<Delta = D>,
        <V as Diff>::Delta: From<V>,
        D: Clone,
    {
        let mut entry = self.entry.as_ref().clone();
        entry.delete(seqno);
        self.entry = Arc::new(entry);
    }

    #[inline]
    pub fn set_red(&mut self) {
        self.black = false
    }

    #[inline]
    pub fn set_black(&mut self) {
        self.black = true
    }

    #[inline]
    pub fn toggle_link(&mut self) {
        self.black = !self.black
    }
}

impl<K, V, D> Node<K, V, D> {
    #[inline]
    pub fn as_left_ref(&self) -> Option<&Node<K, V, D>> {
        self.left.as_ref().map(Deref::deref)
    }

    #[inline]
    pub fn as_right_ref(&self) -> Option<&Node<K, V, D>> {
        self.right.as_ref().map(Deref::deref)
    }

    #[inline]
    pub fn is_black(&self) -> bool {
        self.black
    }

    pub fn as_key(&self) -> &K {
        self.entry.as_key()
    }

    pub fn to_seqno(&self) -> u64 {
        self.entry.to_seqno()
    }

    pub fn is_deleted(&self) -> bool {
        self.entry.is_deleted()
    }
}

impl<K, V, D> From<db::Entry<K, V, D>> for Node<K, V, D> {
    fn from(entry: db::Entry<K, V, D>) -> Node<K, V, D> {
        Node {
            entry: Arc::new(entry),
            black: false,
            left: None,
            right: None,
        }
    }
}

#[cfg(test)]
#[path = "node_test.rs"]
mod node_test;
