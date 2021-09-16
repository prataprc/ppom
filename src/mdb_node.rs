use std::sync::Arc;

// Node corresponds to a single entry in Mdb instance.
#[derive(Clone)]
pub struct Node<K, V> {
    pub key: K,
    pub entry: Arc<Entry<V>>,
    pub black: bool,                    // store: black or red
    pub left: Option<Arc<Node<K, V>>>,  // store: left child
    pub right: Option<Arc<Node<K, V>>>, // store: right child
}

impl<K, V> Node<K, V> {
    pub fn set(&mut self, value: V, seqno: u64)
    where
        K: Clone,
        V: Clone,
    {
        let mut entry = self.entry.as_ref().clone();
        entry.set(value, seqno);
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

impl<K, V> Node<K, V> {
    #[inline]
    pub fn as_left_ref(&self) -> Option<&Node<K, V>> {
        self.left.as_deref()
    }

    #[inline]
    pub fn as_right_ref(&self) -> Option<&Node<K, V>> {
        self.right.as_deref()
    }

    #[inline]
    pub fn is_black(&self) -> bool {
        self.black
    }

    #[inline]
    pub fn as_key(&self) -> &K {
        &self.key
    }

    #[inline]
    pub fn to_seqno(&self) -> u64 {
        self.entry.to_seqno()
    }
}

impl<K, V> From<(K, Entry<V>)> for Node<K, V> {
    fn from((key, entry): (K, Entry<V>)) -> Node<K, V> {
        Node {
            key,
            entry: Arc::new(entry),
            black: false,
            left: None,
            right: None,
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Entry<V> {
    value: V,
    seqno: u64,
}

impl<V> Entry<V> {
    pub fn new(value: V, seqno: u64) -> Self {
        Entry { value, seqno }
    }

    pub fn to_seqno(&self) -> u64 {
        self.seqno
    }

    pub fn to_value(&self) -> V
    where
        V: Clone,
    {
        self.value.clone()
    }

    pub fn into_value(self) -> V {
        self.value
    }

    fn set(&mut self, value: V, seqno: u64) {
        self.value = value;
        self.seqno = seqno;
    }
}

#[cfg(test)]
#[path = "mdb_node_test.rs"]
mod mdb_node_test;
