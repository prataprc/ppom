use arbitrary::Arbitrary;
use rand::{prelude::random, rngs::SmallRng, Rng, SeedableRng};
use structopt::StructOpt;

use std::{ops::Bound, thread, time};

use ppom::Mdb;

/// Command line options.
#[derive(Clone, StructOpt)]
pub struct Opt {
    #[structopt(long = "seed")]
    seed: Option<u128>,

    #[structopt(long = "no-diff")] // default 1M
    no_diff: bool,

    #[structopt(long = "loads", default_value = "1000000")] // default 1M
    loads: usize,

    #[structopt(long = "sets", default_value = "0")] // default 1M
    sets: usize,

    #[structopt(long = "dels", default_value = "0")] // default 1M
    dels: usize,

    #[structopt(long = "gets", default_value = "0")] // default 1M
    gets: usize,

    #[structopt(long = "writers", default_value = "1")]
    writers: usize,

    #[structopt(long = "readers", default_value = "1")]
    readers: usize,
}

fn main() {
    let opts = Opt::from_args();
    let seed = opts.seed.unwrap_or_else(random);
    let mut rng = SmallRng::from_seed(seed.to_le_bytes());

    let index: Mdb<u64, u64, u64> = Mdb::new("perf");

    // initial load
    let start = time::Instant::now();
    for _i in 0..opts.loads {
        let (key, val): (u64, u64) = (rng.gen(), rng.gen());
        index.set(key, val).unwrap();
    }

    println!("loaded {} items in {:?}", opts.loads, start.elapsed());

    let mut handles = vec![];
    for j in 0..opts.writers {
        let (mut opts, index) = (opts.clone(), index.clone());
        opts.gets = 0;
        let seed = seed + ((j as u128) * 100);
        let h = thread::spawn(move || do_incremental(j, seed, opts, index));
        handles.push(h);
    }
    for j in opts.writers..(opts.writers + opts.readers) {
        let (mut opts, index) = (opts.clone(), index.clone());
        opts.sets = 0;
        opts.dels = 0;
        let seed = seed + ((j as u128) * 100);
        let h = thread::spawn(move || do_incremental(j, seed, opts, index));
        handles.push(h);
    }

    for handle in handles.into_iter() {
        handle.join().unwrap()
    }
}

fn do_incremental(j: usize, seed: u128, opts: Opt, index: Mdb<u64, u64, u64>) {
    let mut rng = SmallRng::from_seed(seed.to_le_bytes());

    let start = time::Instant::now();
    let total = opts.sets + opts.dels + opts.gets;
    let mut n = total;
    while n > 0 {
        let op = rng.gen::<usize>() % total;

        let key = rng.gen::<u64>();
        if op < opts.sets && opts.no_diff {
            let val = rng.gen::<u64>();
            index.set(key, val).ok();
        } else if op < opts.sets {
            let val = rng.gen::<u64>();
            index.insert(key, val).ok();
        } else if op < (opts.sets + opts.dels) && opts.no_diff {
            index.remove(&key).ok();
        } else if op < (opts.sets + opts.dels) {
            index.delete(&key).ok();
        } else {
            index.get(&key).ok();
        }
        n -= 1;
    }
    println!(
        "incremental-{} for operations {}, took {:?}",
        j,
        total,
        start.elapsed()
    );

    let start = time::Instant::now();
    let mut n = 0;
    for _e in index.iter().unwrap() {
        n += 1;
    }
    println!("iter-{} for iterating {}, took {:?}", j, n, start.elapsed());
}

#[derive(Clone, Debug, Arbitrary, Eq, PartialEq)]
enum Limit<T> {
    Unbounded,
    Included(T),
    Excluded(T),
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
