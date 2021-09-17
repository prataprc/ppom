use arbitrary::{Arbitrary, Unstructured};
use rand::{prelude::random, rngs::SmallRng, Rng, SeedableRng};

use std::{
    collections::{hash_map::DefaultHasher, BTreeMap},
    convert::TryFrom,
    hash::{Hash, Hasher},
    ops::Bound,
    thread,
};

use super::*;

// TODO: testcase for SetCas RemoveCas, and skewed-remove

#[test]
fn test_unique_hash() {
    let mut hashes = vec![];
    for key in 0..256 {
        let mut hasher = DefaultHasher::new();
        key.hash(&mut hasher);
        hashes.push(hasher.finish());
    }
    hashes.dedup();
    assert!(hashes.len() == 256);
}

#[test]
fn test_mdb_omap() {
    let seed: u128 = random();
    // let seed: u128 = 46462177783710469322936477079324309004;
    let n_load = 100_000; // TODO make it 1_000_000;
    let n_ops = 100_000;
    let n_threads = 16;

    test_with_key_type::<u8>("u8".to_string(), seed, n_load, n_ops, n_threads);
    test_with_key_type::<u32>("u32".to_string(), seed, n_load, n_ops, n_threads);
    test_with_key_type::<u64>("u64".to_string(), seed, n_load, n_ops, n_threads);
}

fn test_with_key_type<K>(
    prefix: String,
    seed: u128,
    n_load: usize,
    n_ops: usize,
    n_threads: usize,
) where
    K: Copy + fmt::Debug + Hash + Arbitrary,
{
    println!("test_with_key_type-{} seed:{}", prefix, seed);
    let mut rng = SmallRng::from_seed(seed.to_le_bytes());

    let index: OMap<u64, u64> = OMap::new();
    let mut btmap: BTreeMap<u64, u64> = BTreeMap::new();

    for _i in 0..n_load {
        let (key, val): (u64, u64) = (rng.gen(), rng.gen());
        btmap.insert(key, val);
        index.set(key, val).unwrap();
    }

    println!(
        "test_with_key_type-{} initial load len:{}/{}",
        prefix,
        index.len(),
        btmap.len()
    );

    let mut handles = vec![];
    for j in 0..n_threads {
        let (a, b) = (index.clone(), btmap.clone());
        let prefix = prefix.clone();
        let h = thread::spawn(move || {
            do_test::<K>(prefix, seed + (j as u128), n_threads, j, n_ops, a, b)
        });
        handles.push(h);
    }

    let mut counts = [0_usize; 7];
    for handle in handles.into_iter() {
        let (cs, refmap) = handle.join().unwrap();
        for (key, val) in refmap.iter() {
            btmap.insert(*key, *val);
        }
        for (i, c) in cs.iter().enumerate() {
            counts[i] += c;
        }
    }

    assert_eq!(index.len(), btmap.len());
    assert_eq!(index.is_empty(), btmap.is_empty());
    // test iter
    counts[3] += 1;
    let a: Vec<(u64, u64)> = index.iter().unwrap().collect();
    let b: Vec<(u64, u64)> = btmap.iter().map(|(k, v)| (*k, *v)).collect();
    assert_eq!(a, b);
    // test range
    for _i in 0..100 {
        let bytes = rng.gen::<[u8; 32]>();
        let mut uns = Unstructured::new(&bytes);

        counts[4] += 1;
        let high: Limit<u64> = uns.arbitrary().unwrap();
        let low: Limit<u64> = uns.arbitrary().unwrap();
        if asc_range(&low, &high) {
            let r = (Bound::from(low), Bound::from(high));
            let a: Vec<(u64, u64)> = index.range(r).unwrap().collect();
            let b: Vec<(u64, u64)> = btmap.range(r).map(|(k, v)| (*k, *v)).collect();
            assert_eq!(a, b, "range {:?}", r);
        } else {
            let r = (Bound::from(low), Bound::from(high));
            let a: Vec<(u64, u64)> = index.range(r).unwrap().collect();
            assert_eq!(a.len(), 0, "range {:?}", r);
        }
    }
    // test reverse
    for _i in 0..100 {
        let bytes = rng.gen::<[u8; 32]>();
        let mut uns = Unstructured::new(&bytes);

        counts[5] += 1;
        let high: Limit<u64> = uns.arbitrary().unwrap();
        let low: Limit<u64> = uns.arbitrary().unwrap();
        if asc_range(&low, &high) {
            let r = (Bound::from(low), Bound::from(high));
            let a: Vec<(u64, u64)> = index.reverse(r).unwrap().collect();
            let b: Vec<(u64, u64)> =
                btmap.range(r).rev().map(|(k, v)| (*k, *v)).collect();
            assert_eq!(a, b, "reverse {:?}", r);
        } else {
            let r = (Bound::from(low), Bound::from(high));
            let a: Vec<(u64, u64)> = index.reverse(r).unwrap().collect();
            assert_eq!(a.len(), 0, "reverse {:?}", r);
        }
    }
    // test validate
    counts[6] += 1;
    index.validate().unwrap();

    println!(
        "test_with_key_type-{} counts {:?} len:{}",
        prefix,
        counts,
        index.len()
    );
}

fn do_test<K>(
    prefix: String,
    seed: u128,
    concur: usize,
    thread: usize,
    n_ops: usize,
    index: OMap<u64, u64>,
    mut btmap: BTreeMap<u64, u64>,
) -> ([usize; 7], BTreeMap<u64, u64>)
where
    K: Copy + fmt::Debug + Hash + Arbitrary,
{
    let mut rng = SmallRng::from_seed(seed.to_le_bytes());
    let mut counts = [0_usize; 7];

    for _i in 0..n_ops {
        let bytes = rng.gen::<[u8; 32]>();
        let mut uns = Unstructured::new(&bytes);

        let op: Op<K, u64> = uns.arbitrary().unwrap();
        // println!("do_test-{} op -- {:?}", prefix, op);
        match op {
            Op::Set(k, val) => {
                counts[0] += 1;
                let key = key_for_thread(k, concur, thread);

                match (index.set(key, val).unwrap(), btmap.insert(key, val)) {
                    (None, None) => (),
                    (Some(v), Some(r)) => assert_eq!(v, r, "for key {}", key),
                    (None, Some(_)) => panic!("set no key {} in omap", key),
                    (Some(v), None) => panic!("set no key {} in btree v:{}", key, v),
                }
            }
            Op::Remove(k) => {
                counts[1] += 1;
                let key = key_for_thread(k, concur, thread);

                match (index.remove(&key).unwrap(), btmap.remove(&key)) {
                    (None, None) => (),
                    (Some(v), Some(r)) => assert_eq!(v, r, "for key {}", key),
                    (None, Some(_)) => panic!("remove no key {} in omap", key),
                    (Some(v), None) => panic!("remove no key {} in btree v:{}", key, v),
                }
            }
            Op::Get(k) => {
                counts[2] += 1;
                let key = key_for_thread(k, concur, thread);

                match (index.get(&key), btmap.get(&key)) {
                    (Err(Error::KeyNotFound(_, _)), None) => (),
                    (Ok((v, _)), Some(r)) => assert_eq!(v, *r, "for key {}", key),
                    (Err(e), Some(_)) => panic!("get no key {} in omap e:{}", key, e),
                    (Ok(_), None) => panic!("get no key {} in btree", key),
                    (Err(e), None) => panic!("get missing key {} e:{}", key, e),
                }
            }
        }
    }

    println!(
        "do_test-{} counts {:?} len:{}/{}",
        prefix,
        counts,
        index.len(),
        btmap.len()
    );
    (counts, btmap)
}

#[derive(Debug, Arbitrary)]
enum Op<K, V> {
    Set(K, V),
    Remove(K),
    Get(K),
}

#[derive(Debug, Eq, PartialEq, Arbitrary)]
enum Limit<T> {
    Unbounded,
    Included(T),
    Excluded(T),
}

fn asc_range<T: PartialOrd>(from: &Limit<T>, to: &Limit<T>) -> bool {
    match (from, to) {
        (Limit::Unbounded, _) => true,
        (_, Limit::Unbounded) => true,
        (Limit::Included(a), Limit::Included(b)) => a <= b,
        (Limit::Included(a), Limit::Excluded(b)) => a <= b,
        (Limit::Excluded(a), Limit::Included(b)) => a <= b,
        (Limit::Excluded(a), Limit::Excluded(b)) => b > a,
    }
}

impl<T> From<Limit<T>> for Bound<T> {
    fn from(limit: Limit<T>) -> Self {
        match limit {
            Limit::Unbounded => Bound::Unbounded,
            Limit::Included(v) => Bound::Included(v),
            Limit::Excluded(v) => Bound::Excluded(v),
        }
    }
}

fn key_for_thread<K>(key: K, concur: usize, thread: usize) -> u64
where
    K: Hash,
{
    let mut hasher = DefaultHasher::new();
    key.hash(&mut hasher);
    let hash: u64 = hasher.finish();

    let w = u64::MAX / u64::try_from(concur).unwrap();
    (u64::try_from(thread).unwrap() * w) + (hash % w)
}
