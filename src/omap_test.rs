use arbitrary::{self, unstructured::Unstructured, Arbitrary};
use rand::{prelude::random, rngs::SmallRng, Rng, SeedableRng};

use super::*;

use std::collections::BTreeMap;

#[test]
fn test_omap() {
    let ops = 1_000_000;
    let seed: u128 = random();
    // let seed: u128 = 46462177783710469322936477079324309004;
    let mut rng = SmallRng::from_seed(seed.to_le_bytes());
    let skew_remove: u8 = rng.gen::<u8>() % 2;
    println!(
        "test_omap seed:{}, ops:{} skew_remove:{}",
        seed, ops, skew_remove
    );

    let mut index: OMap<u8, u64> = OMap::new();
    let mut btmap: BTreeMap<u8, u64> = BTreeMap::new();

    let mut counts = [0_usize; 11];

    for _i in 0..ops {
        let bytes = rng.gen::<[u8; 32]>();
        let mut uns = Unstructured::new(&bytes);

        let op: Op<u8, u64> = uns.arbitrary().unwrap();
        // println!("op -- {:?}", op);
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
            Op::Validate => {
                counts[4] += 1;
                index.validate().unwrap();
            }
            Op::Get(key) => {
                counts[5] += 1;
                match (index.get(&key), btmap.get(&key)) {
                    (None, None) => (),
                    (Some(v), Some(r)) => assert_eq!(v, *r, "for key {}", key),
                    (None, Some(_)) => panic!("get no key {} in omap", key),
                    (Some(_), None) => panic!("get no key {} in btree", key),
                }
            }
            Op::Iter => {
                counts[6] += 1;
                let a: Vec<(u8, u64)> = index.iter().collect();
                let b: Vec<(u8, u64)> = btmap.iter().map(|(k, v)| (*k, *v)).collect();
                assert_eq!(a, b);
            }
            Op::Range((low, high)) if asc_range(&low, &high) => {
                counts[7] += 1;
                let r = (Bound::from(low), Bound::from(high));
                let a: Vec<(u8, u64)> = index.range(r).collect();
                let b: Vec<(u8, u64)> = btmap.range(r).map(|(k, v)| (*k, *v)).collect();
                assert_eq!(a, b, "range {:?}", r);
            }
            Op::Range((low, high)) => {
                counts[7] += 1;
                let r = (Bound::from(low), Bound::from(high));
                let a: Vec<(u8, u64)> = index.range(r).collect();
                assert_eq!(a.len(), 0, "range {:?}", r);
            }
            Op::Reverse((low, high)) if asc_range(&low, &high) => {
                counts[8] += 1;
                let r = (Bound::from(low), Bound::from(high));
                let a: Vec<(u8, u64)> = index.reverse(r).collect();
                let b: Vec<(u8, u64)> =
                    btmap.range(r).rev().map(|(k, v)| (*k, *v)).collect();
                assert_eq!(a, b, "reverse {:?}", r);
            }
            Op::Reverse((low, high)) => {
                counts[8] += 1;
                let r = (Bound::from(low), Bound::from(high));
                let a: Vec<(u8, u64)> = index.reverse(r).collect();
                assert_eq!(a.len(), 0, "reverse {:?}", r);
            }
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
                    None => assert!(btmap.len() == 0, "unexpected len: {}", btmap.len()),
                }
            }
        }

        // skew the ops towards more remove, so that we end up applying ops on empty
        // index.
        match skew_remove {
            0 => (),
            1 => {
                for _i in 0..skew_remove {
                    match index.random(&mut rng) {
                        Some((key, _)) => {
                            match (index.remove(&key), btmap.remove(&key)) {
                                (Some(v), Some(r)) => {
                                    assert_eq!(v, r, "for key {}", key)
                                }
                                (v, r) => panic!("unexpected {:?} != {:?}", v, r),
                            }
                        }
                        None => (),
                    }
                }
            }
            _ => unreachable!(),
        }
    }

    let a: Vec<(u8, u64)> = index.iter().collect();
    let b: Vec<(u8, u64)> = btmap.iter().map(|(k, v)| (*k, *v)).collect();
    assert_eq!(a, b);

    println!("counts {:?} len:{}/{}", counts, index.len(), btmap.len());
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
