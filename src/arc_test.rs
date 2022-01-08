use arbitrary::{self, unstructured::Unstructured, Arbitrary};
use rand::{prelude::random, rngs::SmallRng, Rng, SeedableRng};

use super::*;

use std::{collections::BTreeMap, ops::Bound, thread};

#[test]
fn test_arc_omap() {
    let seed: u64 = random();
    // let seed: u64 = 46462177783710469322936477079324309004;
    println!("test_arc_omap {}", seed);
    let mut rng = SmallRng::seed_from_u64(seed);

    let mut index: OMap<u8, u64> = OMap::new();
    let mut btmap: BTreeMap<u8, u64> = BTreeMap::new();

    for _i in 0..1_000_000 {
        let (key, val): (u8, u64) = (rng.gen(), rng.gen());
        btmap.insert(key, val);
        index = index.set(key, val);
    }

    println!(
        "test_arc_omap initial load len:{}/{}",
        index.len(),
        btmap.len()
    );

    let mut handles = vec![];
    for j in 0..16 {
        let (a, b) = (index.clone(), btmap.clone());
        let h = thread::spawn(move || do_test(j, seed + (j as u64), 1_000_000, a, b));
        handles.push(h);
    }

    for handle in handles.into_iter() {
        handle.join().unwrap();
    }

    assert_eq!(index.len(), btmap.len());

    for ((a, b), (x, y)) in index.iter().zip(btmap.iter()) {
        assert_eq!(a, *x);
        assert_eq!(b, *y, "for key {}", a);
    }
}

fn do_test(
    _thread: usize,
    seed: u64,
    n: usize,
    mut index: OMap<u8, u64>,
    mut btmap: BTreeMap<u8, u64>,
) {
    let mut rng = SmallRng::seed_from_u64(seed);

    let mut counts = [0_usize; 10];

    for _i in 0..n {
        let bytes = rng.gen::<[u8; 32]>();
        let mut uns = Unstructured::new(&bytes);

        let op: Op<u8, u64> = uns.arbitrary().unwrap();
        // println!("test_arc_omap.do_test {}-op -- {:?}", _j, op);
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
                let res_bt = btmap.insert(key, val);
                let new_index = index.set(key, val);
                match (index.get(&key), res_bt) {
                    (None, None) => (),
                    (Some(v), Some(r)) => assert_eq!(v, r, "old val for key {}", key),
                    (None, Some(_)) => panic!("no key {} in omap", key),
                    (Some(_), None) => panic!("no key {} in btree", key),
                }
                match (new_index.get(&key), btmap.get(&key)) {
                    (None, None) => unreachable!(),
                    (Some(v), Some(r)) => assert_eq!(v, *r, "for key {}", key),
                    (None, Some(_)) => panic!("no key {} in omap", key),
                    (Some(_), None) => panic!("no key {} in btree", key),
                }
                index = new_index;
            }
            Op::Remove(key) => {
                counts[3] += 1;
                let res_bt = btmap.remove(&key);
                let new_index = index.remove(&key);
                match (index.get(&key), res_bt) {
                    (None, None) => (),
                    (Some(v), Some(r)) => assert_eq!(v, r, "for remove key {}", key),
                    (None, Some(_)) => panic!("no key {} in omap", key),
                    (Some(_), None) => panic!("no key {} in btree", key),
                }
                match (new_index.get(&key), btmap.get(&key)) {
                    (None, None) => (),
                    (Some(_), Some(_)) => unreachable!(),
                    (None, Some(_)) => unreachable!(),
                    (Some(_), None) => unreachable!(),
                }
                index = new_index;
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
                assert_eq!(index.range(r).count(), 0, "range {:?}", r);
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
                assert_eq!(index.reverse(r).count(), 0, "reverse {:?}", r);
            }
        }
    }

    let a: Vec<(u8, u64)> = index.iter().collect();
    let b: Vec<(u8, u64)> = btmap.iter().map(|(k, v)| (*k, *v)).collect();
    assert_eq!(a, b);

    println!(
        "test_arc_omap.do_test counts {:?} len:{}/{}",
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
