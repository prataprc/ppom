use arbitrary::{self, unstructured::Unstructured, Arbitrary};
use rand::{prelude::random, rngs::SmallRng, Rng, SeedableRng};

use super::*;

use std::collections::BTreeMap;

#[test]
fn test_simple_omap() {
    let n_ops = 1_000_000;
    let seed: u64 = random();
    // let seed: u64 = 194689585675773936160943145888738646518;

    run_with_key::<u8>("u8-key", seed, n_ops, 2);
    run_with_key::<u16>("16-key", seed, n_ops, 5000);
    run_with_key::<u32>("32-key", seed, n_ops, 5000);
}

fn run_with_key<K>(prefix: &str, seed: u64, n_ops: usize, iter_clamp: usize)
where
    K: Ord + Copy + Clone + PartialEq + std::fmt::Display + std::fmt::Debug + Arbitrary,
{
    let mut rng = SmallRng::seed_from_u64(seed);
    let skew_remove: u8 = rng.gen::<u8>() % 2;
    println!(
        "test_simple_omap.run_with_key {} seed:{}, n_ops:{} skew_remove:{}",
        prefix, seed, n_ops, skew_remove
    );

    let mut index: OMap<K, u64> = OMap::new();
    let mut btmap: BTreeMap<K, u64> = BTreeMap::new();

    let mut counts = [0_usize; 11];

    for i in 0..n_ops {
        let bytes = rng.gen::<[u8; 32]>();
        let mut uns = Unstructured::new(&bytes);

        let op: Op<K, u64> = uns.arbitrary().unwrap();
        // println!("test_simple_omap.run_with_key op -- {:?}", op);
        match op {
            Op::Len => {
                counts[0] += 1;
                assert_eq!(index.len(), btmap.len());
            }
            Op::IsEmpty => {
                counts[1] += 1;
                assert_eq!(index.is_empty(), btmap.is_empty());
            }
            Op::Set(key, val) => {
                counts[2] += 1;
                match (index.set(key, val), btmap.insert(key, val)) {
                    (None, None) => (),
                    (Some(v), Some(r)) => assert_eq!(v, r, "for key {}", key),
                    (None, Some(_)) => panic!("set no key {} in omap", key),
                    (Some(_), None) => panic!("set no key {} in btree", key),
                }
            }
            Op::Remove(key) => {
                counts[3] += 1;
                match (index.remove(&key), btmap.remove(&key)) {
                    (None, None) => (),
                    (Some(v), Some(r)) => assert_eq!(v, r, "for key {}", key),
                    (None, Some(_)) => panic!("remove no key {} in omap", key),
                    (Some(_), None) => panic!("remove no key {} in btree", key),
                }
            }
            Op::Validate if (i % iter_clamp) == 0 => {
                counts[4] += 1;
                index.validate().unwrap();
            }
            Op::Validate => (),
            Op::Get(key) => {
                counts[5] += 1;
                match (index.get(&key), btmap.get(&key)) {
                    (None, None) => (),
                    (Some(v), Some(r)) => assert_eq!(v, *r, "for key {}", key),
                    (None, Some(_)) => panic!("get no key {} in omap", key),
                    (Some(_), None) => panic!("get no key {} in btree", key),
                }
            }
            Op::Iter if (i % iter_clamp) == 0 => {
                counts[6] += 1;
                let a: Vec<(K, u64)> = index.iter().collect();
                let b: Vec<(K, u64)> = btmap.iter().map(|(k, v)| (*k, *v)).collect();
                assert_eq!(a, b);
            }
            Op::Iter => (),
            Op::Range((low, high)) if asc_range(&low, &high) && (i % iter_clamp) == 0 => {
                counts[7] += 1;
                let r = (Bound::from(low), Bound::from(high));
                let a: Vec<(K, u64)> = index.range(r).collect();
                let b: Vec<(K, u64)> = btmap.range(r).map(|(k, v)| (*k, *v)).collect();
                assert_eq!(a, b, "range {:?}", r);
            }
            Op::Range((low, high)) if (i % iter_clamp) == 0 => {
                counts[7] += 1;
                let r = (Bound::from(low), Bound::from(high));
                assert_eq!(index.range(r).count(), 0, "range {:?}", r);
            }
            Op::Range((_, _)) => (),
            Op::Reverse((low, high))
                if asc_range(&low, &high) && (i % iter_clamp) == 0 =>
            {
                counts[8] += 1;
                let r = (Bound::from(low), Bound::from(high));
                let a: Vec<(K, u64)> = index.reverse(r).collect();
                let b: Vec<(K, u64)> =
                    btmap.range(r).rev().map(|(k, v)| (*k, *v)).collect();
                assert_eq!(a, b, "reverse {:?}", r);
            }
            Op::Reverse((low, high)) if (i % iter_clamp) == 0 => {
                counts[8] += 1;
                let r = (Bound::from(low), Bound::from(high));
                assert_eq!(index.reverse(r).count(), 0, "reverse {:?}", r);
            }
            Op::Reverse((_, _)) => (),
            Op::Extend(items) => {
                counts[9] += 1;
                index.extend(items.clone());
                btmap.extend(items.clone())
            }
            Op::Random => {
                counts[10] += 1;
                match index.random(&mut rng) {
                    Some((key, value)) => match btmap.get(&key) {
                        Some(val) => assert_eq!(value, *val, "for key {:?}", key),
                        None => panic!("key missing {:?}", key),
                    },
                    None => assert!(btmap.is_empty(), "unexpected len: {}", btmap.len()),
                }
            }
        }

        // skew the ops towards more remove, so that we end up applying ops on empty
        // index.
        match skew_remove {
            0 => (),
            1 => {
                for _i in 0..skew_remove {
                    if let Some((key, _)) = index.random(&mut rng) {
                        match (index.remove(&key), btmap.remove(&key)) {
                            (Some(v), Some(r)) => {
                                assert_eq!(v, r, "for key {}", key)
                            }
                            (v, r) => panic!("unexpected {:?} != {:?}", v, r),
                        }
                    }
                }
            }
            _ => unreachable!(),
        }
    }

    let a: Vec<(K, u64)> = index.iter().collect();
    let b: Vec<(K, u64)> = btmap.iter().map(|(k, v)| (*k, *v)).collect();
    assert_eq!(a, b);

    println!(
        "test_simple_omap.run_with_key counts {:?} len:{}/{}",
        counts,
        index.len(),
        btmap.len()
    );
}

#[derive(Debug, Arbitrary)]
enum Op<K, V> {
    Len,
    IsEmpty,
    Set(K, V),
    Remove(K),
    Get(K),
    Iter,
    Range((Limit<K>, Limit<K>)),
    Reverse((Limit<K>, Limit<K>)),
    Extend(Vec<(K, V)>),
    Random,
    Validate,
}

#[derive(Debug, Arbitrary, Eq, PartialEq)]
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
