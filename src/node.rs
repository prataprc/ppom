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

//// TODO: test cases for Depth.
//
///// Statistic type, that captures minimum, maximum, average and percentile of
///// leaf-node depth in the LLRB tree.
//#[derive(Clone)]
//pub struct LlrbDepth {
//    pub samples: usize,
//    pub min: usize,
//    pub max: usize,
//    pub total: usize,
//    pub depths: [u64; 256],
//}
//
//impl LlrbDepth {
//    pub(crate) fn sample(&mut self, depth: usize) {
//        self.samples += 1;
//        self.total += depth;
//        self.min = usize::min(self.min, depth);
//        self.max = usize::max(self.max, depth);
//        self.depths[depth] += 1;
//    }
//
//    /// Return number of leaf-nodes sample for depth in LLRB tree.
//    pub fn to_samples(&self) -> usize {
//        self.samples
//    }
//
//    /// Return minimum depth of leaf-node in LLRB tree.
//    pub fn to_min(&self) -> usize {
//        self.min
//    }
//
//    /// Return the average depth of leaf-nodes in LLRB tree.
//    pub fn to_mean(&self) -> usize {
//        self.total / self.samples
//    }
//
//    /// Return maximum depth of leaf-node in LLRB tree.
//    pub fn to_max(&self) -> usize {
//        self.max
//    }
//
//    /// Return depth as tuple of percentiles, each tuple provides
//    /// (percentile, depth). Returned percentiles from 91 .. 99
//    pub fn to_percentiles(&self) -> Vec<(u8, usize)> {
//        let mut percentiles: Vec<(u8, usize)> = vec![];
//        let (mut acc, mut prev_perc) = (0_u64, 90_u8);
//        let iter = self.depths.iter().enumerate().filter(|(_, &item)| item > 0);
//        for (depth, samples) in iter {
//            acc += *samples;
//            let perc = ((acc as f64 / (self.samples as f64)) * 100_f64) as u8;
//            if perc > prev_perc {
//                percentiles.push((perc, depth));
//                prev_perc = perc;
//            }
//        }
//        percentiles
//    }
//
//    pub fn merge(self, other: Self) -> Self {
//        let mut depths = LlrbDepth {
//            samples: self.samples + other.samples,
//            min: cmp::min(self.min, other.min),
//            max: cmp::max(self.max, other.max),
//            total: self.total + other.total,
//            depths: [0; 256],
//        };
//        for i in 0..depths.depths.len() {
//            depths.depths[i] = self.depths[i] + other.depths[i];
//        }
//        depths
//    }
//}
//
//impl fmt::Display for LlrbDepth {
//    fn fmt(&self, f: &mut fmt::Formatter) -> result::Result<(), fmt::Error> {
//        let (m, n, x) = (self.to_min(), self.to_mean(), self.to_max());
//        let props: Vec<String> = self
//            .to_percentiles()
//            .into_iter()
//            .map(|(perc, depth)| format!(r#""{}" = {}"#, perc, depth))
//            .collect();
//        let depth = props.join(", ");
//
//        write!(
//            f,
//            concat!(
//                "{{ samples={}, min={}, mean={}, max={}, ",
//                "percentiles={{ {} }} }}"
//            ),
//            self.samples, m, n, x, depth
//        )
//    }
//}
//
//impl ToJson for LlrbDepth {
//    fn to_json(&self) -> String {
//        let props: Vec<String> = self
//            .to_percentiles()
//            .into_iter()
//            .map(|(d, n)| format!(r#""{}": {}"#, d, n))
//            .collect();
//        let strs = [
//            format!(r#""samples": {}"#, self.to_samples()),
//            format!(r#""min": {}"#, self.to_min()),
//            format!(r#""mean": {}"#, self.to_mean()),
//            format!(r#""max": {}"#, self.to_max()),
//            format!(r#""percentiles": {{ {} }}"#, props.join(", ")),
//        ];
//        format!(r#"{{ {} }}"#, strs.join(", "))
//    }
//}
//
//impl Default for LlrbDepth {
//    fn default() -> Self {
//        LlrbDepth {
//            samples: 0,
//            min: std::usize::MAX,
//            max: std::usize::MIN,
//            total: 0,
//            depths: [0; 256],
//        }
//    }
//}
