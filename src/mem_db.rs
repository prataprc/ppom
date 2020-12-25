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

use mkit::spinlock::Spinlock;

use std::sync::Arc;

use crate::node::Node;

/// Mdb type for thread-safe, concurrent reads and serialized writes.
///
/// [mvcc]: https://en.wikipedia.org/wiki/Multiversion_concurrency_control
/// [llrb]: https://en.wikipedia.org/wiki/Left-leaning_red-black_tree
#[derive(Clone)]
pub struct Mdb<K, V, D> {
    name: String,
    lsm: bool,
    sticky: bool,

    inner: Arc<Spinlock<Inner<K, V, D>>>,
}

#[derive(Clone)]
struct Inner<K, V, D> {
    root: Option<Node<K, V, D>>,
    seqno: u64,
    n_count: usize,
    n_deleted: usize,
}

//impl<K, V, D> TryFrom<Omap<K, V>> for Mdb<K, V, D> {
//    fn try_from(m: Omap<K, V>) -> Self {
//        todo!()
//    }
//}

impl<K, V, D> for Mdb<K, V, D> {
    fn new(name: &str, lsm: bool, stick: bool) -> Mdb<K, V, D> {
        let inner = Inner {
            root: None,
            seqno: 0,
            n_count: 0,
            n_deleted: 0,
        };

        Mdb {
            name: name.to_string(),
            lsm,
            sticky,

            inner: Arc::new(Spinlock::new(inner)),
        }
    }
}
