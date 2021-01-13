use arbitrary::{self, unstructured::Unstructured, Arbitrary};
use rand::{prelude::random, rngs::SmallRng, Rng, SeedableRng};

use super::*;

use std::{collections::BTreeMap, ops::Bound, thread};

type Entry = db::Entry<u16, u64, u64>;

#[test]
fn test_mdb_nodiff() {
    let seed: u128 = random();
    // let seed: u128 = 306171699234476756746827099155462650145;
    println!("test_mdb_nodiff seed {}", seed);
    let mut rng = SmallRng::from_seed(seed.to_le_bytes());

    let n_init = 100_000;
    let n_incr = 100_000;
    let n_threads = 16;

    let index: Mdb<u16, u64, u64> = Mdb::new("test_diff");
    let mut btmap: BTreeMap<u16, Entry> = BTreeMap::new();

    for _i in 0..n_init {
        let (key, val): (u16, u64) = (rng.gen(), rng.gen());
        let Wr { seqno, .. } = index.set(key, val).unwrap();
        btmap.insert(key, Entry::new(key, val, seqno));
    }

    println!("initial load len:{}/{}", index.len(), btmap.len());

    let mut handles = vec![];
    for j in 0..n_threads {
        let (a, b) = (index.clone(), btmap.clone());
        let seed = seed + ((j as u128) * 100);
        let h = thread::spawn(move || do_nodiff_test(j, seed, n_incr, a, b));
        handles.push(h);
    }

    let mut btmap = BTreeMap::new();
    for handle in handles.into_iter() {
        btmap = merge_btmap([btmap, handle.join().unwrap()]);
    }

    let mut n_count = 0;
    for (key, val) in btmap.iter() {
        match val.value {
            db::Value::U { value, seqno } => {
                // println!("verify {} {} {}", key, value, seqno);
                let entry = index.get(key).unwrap();
                assert_eq!(value, entry.to_value().unwrap(), "{}", key);
                assert_eq!(seqno, entry.to_seqno());
                n_count += 1;
            }
            db::Value::D { .. } => assert!(index.get(key).is_err()),
        }
    }

    assert_eq!(index.len(), n_count);
}

#[test]
fn test_mdb_diff() {
    let seed: u128 = random();
    // let seed: u128 = 231762160918118338780311754609780190356;
    println!("test_mdb_diff seed {}", seed);
    let mut rng = SmallRng::from_seed(seed.to_le_bytes());

    let n_init = 100_000;
    let n_incr = 100_000;
    let n_threads = 16;

    let index: Mdb<u16, u64, u64> = Mdb::new("test_nodiff");
    let mut btmap: BTreeMap<u16, Entry> = BTreeMap::new();

    for _i in 0..n_init {
        let (key, val): (u16, u64) = (rng.gen(), rng.gen());
        let Wr { seqno, .. } = index.insert(key, val).unwrap();
        match btmap.get_mut(&key) {
            Some(entry) => entry.insert(val, seqno),
            None => {
                btmap.insert(key, Entry::new(key, val, seqno));
            }
        };
    }

    println!("initial load len:{}/{}", index.len(), btmap.len());

    let mut handles = vec![];
    for j in 0..n_threads {
        let (a, b) = (index.clone(), btmap.clone());
        let seed = seed + ((j as u128) * 100);
        let h = thread::spawn(move || do_diff_test(j, seed, n_incr, a, b));
        handles.push(h);
    }

    let mut btmap = BTreeMap::new();
    for handle in handles.into_iter() {
        btmap = merge_btmap([btmap, handle.join().unwrap()]);
    }
    for (key, val) in btmap.iter_mut() {
        let mut values = val.to_values();
        values.dedup();
        *val = Entry::from((key.clone(), values));
    }

    assert_eq!(index.len(), btmap.len());

    for (val, (x, y)) in index.iter().unwrap().zip(btmap.iter()) {
        assert_eq!(val.as_key(), x);
        assert_eq!(val, *y, "for key {}", val.as_key());
    }
}

fn do_nodiff_test(
    j: usize,
    seed: u128,
    n: usize,
    index: Mdb<u16, u64, u64>,
    mut btmap: BTreeMap<u16, Entry>,
) -> BTreeMap<u16, Entry> {
    let mut rng = SmallRng::from_seed(seed.to_le_bytes());

    let mut counts = [0_usize; 14];

    for _i in 0..n {
        let bytes = rng.gen::<[u8; 32]>();
        let mut uns = Unstructured::new(&bytes);

        let op: NodiffOp<u16, u64> = uns.arbitrary().unwrap();
        let (_seqno, _cas) = match op.clone() {
            NodiffOp::Set(key, val) => {
                counts[0] += 1;
                let Wr { seqno, .. } = index.set(key, val).unwrap();
                btmap.insert(key, Entry::new(key, val, seqno));
                (seqno, 0)
            }
            NodiffOp::SetCas(key, val) => {
                counts[1] += 1;
                let cas = index.get(&key).map(|e| e.to_seqno()).unwrap_or(0);
                match index.set_cas(key, val, cas) {
                    Ok(Wr { seqno, .. }) => {
                        btmap.insert(key, Entry::new(key, val, seqno));
                        (seqno, cas)
                    }
                    Err(_) => {
                        counts[2] += 1;
                        (0, cas)
                    }
                }
            }
            NodiffOp::Remove(key) => {
                counts[3] += 1;
                match index.remove(&key) {
                    Ok(Wr {
                        seqno,
                        old_entry: Some(_),
                    }) => {
                        btmap.insert(key, Entry::new_deleted(key, seqno));
                        (seqno, 0)
                    }
                    _ => (0, 0),
                }
            }
            NodiffOp::RemoveCas(key) => {
                counts[4] += 1;
                let cas = index.get(&key).map(|e| e.to_seqno()).unwrap_or(0);
                match index.remove_cas(&key, cas) {
                    Err(Error::InvalidCAS(_, _)) => {
                        counts[5] += 1;
                        (0, cas)
                    }
                    Err(err) => panic!("{}", err),
                    Ok(Wr {
                        seqno,
                        old_entry: Some(_),
                    }) => {
                        btmap.insert(key, Entry::new_deleted(key, seqno));
                        (seqno, cas)
                    }
                    Ok(_) => (0, cas),
                }
            }
            NodiffOp::Get(key) => {
                counts[8] += 1;
                index.get(&key).ok();
                (0, 0)
            }
            NodiffOp::Iter => {
                counts[9] += 1;
                let _: Vec<Entry> = index.iter().unwrap().collect();
                (0, 0)
            }
            NodiffOp::Range((l, h)) if asc_range(&l, &h) => {
                counts[10] += 1;
                let r = (Bound::from(l), Bound::from(h));
                let _: Vec<Entry> = index.range(r.clone()).unwrap().collect();
                (0, 0)
            }
            NodiffOp::Reverse((l, h)) if asc_range(&l, &h) => {
                counts[11] += 1;
                let r = (Bound::from(l), Bound::from(h));
                let _: Vec<Entry> = index.reverse(r.clone()).unwrap().collect();
                (0, 0)
            }
            NodiffOp::Range((_, _)) | NodiffOp::Reverse((_, _)) => {
                counts[12] += 1;
                (0, 0)
            }
            NodiffOp::Validate => {
                counts[13] += 1;
                index.validate().unwrap();
                (0, 0)
            }
        };
        // println!("{}-op -- {:?} seqno:{} cas:{}", j, op, _seqno, _cas);
    }

    println!(
        "{} counts {:?} len:{}/{}",
        j,
        counts,
        index.len(),
        btmap.len()
    );
    btmap
}

fn do_diff_test(
    j: usize,
    seed: u128,
    n: usize,
    index: Mdb<u16, u64, u64>,
    mut btmap: BTreeMap<u16, Entry>,
) -> BTreeMap<u16, Entry> {
    let mut rng = SmallRng::from_seed(seed.to_le_bytes());

    let mut counts = [0_usize; 12];

    for _i in 0..n {
        let bytes = rng.gen::<[u8; 32]>();
        let mut uns = Unstructured::new(&bytes);

        let op: DiffOp<u16, u64> = uns.arbitrary().unwrap();
        // println!("{}-op -- {:?}", j, op);
        match op {
            DiffOp::Insert(key, val) => {
                counts[0] += 1;
                let Wr { seqno, old_entry } = index.insert(key, val).unwrap();
                let val = match btmap.get(&key).cloned() {
                    Some(mut e) => {
                        e.insert(val, seqno);
                        e
                    }
                    None => Entry::new(key, val, seqno),
                };
                compare_old_entry(old_entry, btmap.insert(key, val));
            }
            DiffOp::InsertCas(key, val) => {
                counts[1] += 1;
                let cas = index.get(&key).map(|e| e.to_seqno()).unwrap_or(0);
                match index.insert_cas(key, val, cas) {
                    Ok(Wr { seqno, old_entry }) => {
                        let val = match btmap.get(&key).cloned() {
                            Some(mut e) => {
                                e.insert(val, seqno);
                                e
                            }
                            None => Entry::new(key, val, seqno),
                        };
                        compare_old_entry(old_entry, btmap.insert(key, val));
                    }
                    Err(_) => {
                        counts[2] += 1;
                    }
                };
            }
            DiffOp::Delete(key) => {
                counts[3] += 1;
                let Wr { seqno, old_entry } = index.delete(&key).unwrap();
                let val = match btmap.get(&key).cloned() {
                    Some(mut e) => {
                        e.delete(seqno);
                        e
                    }
                    None => Entry::new_deleted(key, seqno),
                };
                compare_old_entry(old_entry, btmap.insert(key, val));
            }
            DiffOp::DeleteCas(key) => {
                counts[4] += 1;
                let cas = index.get(&key).map(|e| e.to_seqno()).unwrap_or(0);
                match index.delete_cas(&key, cas) {
                    Ok(Wr { seqno, old_entry }) => {
                        let val = match btmap.get(&key).cloned() {
                            Some(mut e) => {
                                e.delete(seqno);
                                e
                            }
                            None => Entry::new_deleted(key, seqno),
                        };
                        compare_old_entry(old_entry, btmap.insert(key, val));
                    }
                    Err(Error::InvalidCAS(_, _)) => {
                        counts[5] += 1;
                    }
                    Err(err) => panic!("{}", err),
                };
            }
            DiffOp::Get(key) => {
                counts[6] += 1;
                match (index.get(&key), btmap.get(&key)) {
                    (Err(Error::KeyNotFound(_, _)), None) => (),
                    (Err(err), _) => panic!("{}", err),
                    (Ok(e), Some(x)) => assert!(e.contains(x)),
                    (Ok(_), None) => (),
                }
            }
            DiffOp::Iter => {
                counts[7] += 1;
                for (key, val) in btmap.iter() {
                    assert!(index.get(key).unwrap().contains(val))
                }
            }
            DiffOp::Range((l, h)) if asc_range(&l, &h) => {
                counts[8] += 1;
                let r = (Bound::from(l), Bound::from(h));
                compare_iter(j, index.range(r.clone()).unwrap(), btmap.range(r), true);
            }
            DiffOp::Reverse((l, h)) if asc_range(&l, &h) => {
                counts[9] += 1;
                let r = (Bound::from(l), Bound::from(h));
                compare_iter(
                    j,
                    index.reverse(r.clone()).unwrap(),
                    btmap.range(r).rev(),
                    false,
                );
            }
            DiffOp::Range((_, _)) | DiffOp::Reverse((_, _)) => {
                counts[10] += 1;
            }
            DiffOp::Validate => {
                counts[11] += 1;
                index.validate().unwrap();
            }
        }
    }

    println!(
        "{} counts {:?} len:{}/{}",
        j,
        counts,
        index.len(),
        btmap.len()
    );

    btmap
}

#[derive(Clone, Debug, Arbitrary)]
enum NodiffOp<K, V> {
    Set(K, V),
    SetCas(K, V),
    Remove(K),
    RemoveCas(K),
    Get(K),
    Iter,
    Range((Limit<K>, Limit<K>)),
    Reverse((Limit<K>, Limit<K>)),
    Validate,
}

#[derive(Clone, Debug, Arbitrary)]
enum DiffOp<K, V> {
    Insert(K, V),
    InsertCas(K, V),
    Delete(K),
    DeleteCas(K),
    Get(K),
    Iter,
    Range((Limit<K>, Limit<K>)),
    Reverse((Limit<K>, Limit<K>)),
    Validate,
}

#[derive(Clone, Debug, Arbitrary, Eq, PartialEq)]
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

fn merge_btmap(items: [BTreeMap<u16, Entry>; 2]) -> BTreeMap<u16, Entry> {
    let [one, mut two] = items;

    let mut thr = BTreeMap::new();
    for (key, oe) in one.iter() {
        let val = match two.get(key) {
            Some(te) => oe.merge(te),
            None => oe.clone(),
        };
        two.remove(key);
        thr.insert(key.clone(), val);
    }
    for (key, val) in two.iter() {
        let val = match thr.get(key) {
            Some(v) => val.merge(v),
            None => val.clone(),
        };
        thr.insert(key.clone(), val);
    }

    thr
}

fn compare_iter<'a>(
    j: usize,
    mut index: impl Iterator<Item = Entry>,
    btmap: impl Iterator<Item = (&'a u16, &'a Entry)>,
    frwrd: bool,
) {
    for (_key, val) in btmap {
        loop {
            let e = index.next();
            match e {
                Some(e) => match e.as_key().cmp(val.as_key()) {
                    Ordering::Equal => {
                        assert!(e.contains(&val));
                        break;
                    }
                    Ordering::Less if frwrd => (),
                    Ordering::Greater if !frwrd => (),
                    Ordering::Less | Ordering::Greater => {
                        panic!("{} error miss entry {} {}", j, e.as_key(), val.as_key())
                    }
                },
                None => panic!("{} error missing entry", j),
            }
        }
    }
}

fn compare_old_entry(index: Option<Entry>, btmap: Option<Entry>) {
    match (index, btmap) {
        (None, None) | (Some(_), None) => (),
        (None, Some(btmap)) => panic!("{:?}", btmap),
        (Some(e), Some(x)) => assert!(e.contains(&x)),
    }
}
