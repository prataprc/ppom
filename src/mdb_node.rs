use std::{ops::Deref, sync::Arc};

use mkit::{data::Diff, db};

// Node corresponds to a single entry in Llrb instance.
#[derive(Clone)]
pub struct Node<K, V, D> {
    pub entry: db::Entry<K, V, D>,
    pub black: bool,                       // store: black or red
    pub left: Option<Arc<Node<K, V, D>>>,  // store: left child
    pub right: Option<Arc<Node<K, V, D>>>, // store: right child
}

impl<K, V, D> Node<K, V, D> {
    pub fn set(&mut self, value: V, seqno: u64) {
        self.entry.value.set(value, seqno)
    }

    pub fn insert(&mut self, value: V, seqno: u64)
    where
        V: Clone + Diff<Delta = D>,
    {
        self.entry.insert(value, seqno)
    }

    pub fn delete(&mut self, seqno: u64)
    where
        V: Clone + Diff<Delta = D>,
        <V as Diff>::Delta: From<V>,
    {
        self.entry.delete(seqno)
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
    pub fn as_left_deref(&self) -> Option<&Node<K, V, D>> {
        self.left.as_ref().map(Deref::deref)
    }

    #[inline]
    pub fn as_right_deref(&self) -> Option<&Node<K, V, D>> {
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
            entry,
            black: false,
            left: None,
            right: None,
        }
    }
}

//#[cfg(test)]
//#[path = "mdb_node_test.rs"]
//mod mdb_node_test;
