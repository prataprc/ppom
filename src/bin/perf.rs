use arbitrary::Arbitrary;
use rand::{prelude::random, rngs::SmallRng, Rng, SeedableRng};
use structopt::StructOpt;

use std::{ops::Bound, thread, time};

use ppom::{arc::OMap as OMapArc, rc::OMap as OMapRc, OMap};

/// Command line options.
#[derive(Clone, StructOpt)]
pub struct Opt {
    #[structopt(long = "seed")]
    seed: Option<u128>,

    #[structopt(long = "omap")]
    omap: bool,

    #[structopt(long = "rc-omap")]
    rc_omap: bool,

    #[structopt(long = "arc-omap")]
    arc_omap: bool,

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

    if opts.omap {
        perf_omap(opts, seed);
    } else if opts.rc_omap {
        perf_omap_rc(opts, seed);
    } else if opts.arc_omap {
        perf_omap_arc(opts, seed);
    } else {
        println!("supply --omap or --rc-omap or --arc-omap");
    }
}

fn perf_omap(opts: Opt, seed: u128) {
    let mut rng = SmallRng::from_seed(seed.to_le_bytes());

    let mut index: OMap<u64, u64> = OMap::new();

    // initial load
    let start = time::Instant::now();
    for _i in 0..opts.loads {
        let (key, val): (u64, u64) = (rng.gen(), rng.gen());
        index.set(key, val);
    }

    println!("loaded {} items in {:?}", opts.loads, start.elapsed());

    incr_omap(0, seed, opts, index);
}

fn incr_omap(j: usize, seed: u128, opts: Opt, mut index: OMap<u64, u64>) {
    let mut rng = SmallRng::from_seed(seed.to_le_bytes());

    let start = time::Instant::now();
    let total = opts.sets + opts.dels + opts.gets;
    let mut n = total;
    while n > 0 {
        let op = rng.gen::<usize>() % total;

        let key = rng.gen::<u64>();
        if op < opts.sets {
            let val = rng.gen::<u64>();
            index.set(key, val);
        } else if op < (opts.sets + opts.dels) {
            index.remove(&key);
        } else {
            index.get(&key);
        }
        n -= 1;
    }
    println!(
        "incremental-{} for {} operations took {:?}",
        j,
        total,
        start.elapsed()
    );

    let (elapsed, n) = {
        let start = time::Instant::now();
        let n: usize = index.iter().map(|_| 1_usize).sum();
        assert!(n == index.len(), "{} != {}", n, index.len());
        (start.elapsed(), n)
    };
    println!("iter-{} for iterating {} items, took {:?}", j, n, elapsed);

    let (elapsed, n) = {
        let start = time::Instant::now();
        let n: usize = index.range(..).map(|_| 1_usize).sum();
        assert!(n == index.len(), "{} != {}", n, index.len());
        (start.elapsed(), n)
    };
    println!("range-{} for ranging {} items, took {:?}", j, n, elapsed);

    let (elapsed, n) = {
        let start = time::Instant::now();
        let n: usize = index.reverse(..).map(|_| 1_usize).sum();
        assert!(n == index.len(), "{} != {}", n, index.len());
        (start.elapsed(), n)
    };
    println!(
        "reverse-{} for reverse iterating {} items, took {:?}",
        j, n, elapsed
    );
}

fn perf_omap_rc(opts: Opt, seed: u128) {
    let mut rng = SmallRng::from_seed(seed.to_le_bytes());

    let mut index: OMapRc<u64, u64> = OMapRc::new();

    // initial load
    let start = time::Instant::now();
    for _i in 0..opts.loads {
        let (key, val): (u64, u64) = (rng.gen(), rng.gen());
        index = index.set(key, val);
    }

    println!("loaded {} items in {:?}", opts.loads, start.elapsed());

    incr_omap_rc(0, seed, opts, index);
}

fn incr_omap_rc(j: usize, seed: u128, opts: Opt, mut index: OMapRc<u64, u64>) {
    let mut rng = SmallRng::from_seed(seed.to_le_bytes());

    let start = time::Instant::now();
    let total = opts.sets + opts.dels + opts.gets;
    let mut n = total;
    while n > 0 {
        let op = rng.gen::<usize>() % total;

        let key = rng.gen::<u64>();
        if op < opts.sets {
            let val = rng.gen::<u64>();
            index = index.set(key, val);
        } else if op < (opts.sets + opts.dels) {
            index = index.remove(&key);
        } else {
            index.get(&key);
        }
        n -= 1;
    }
    println!(
        "incremental-{} for {} operations took {:?}",
        j,
        total,
        start.elapsed()
    );

    let (elapsed, n) = {
        let start = time::Instant::now();
        let n: usize = index.iter().map(|_| 1_usize).sum();
        assert!(n == index.len(), "{} != {}", n, index.len());
        (start.elapsed(), n)
    };
    println!("iter-{} for iterating {} items, took {:?}", j, n, elapsed);

    let (elapsed, n) = {
        let start = time::Instant::now();
        let n: usize = index.range(..).map(|_| 1_usize).sum();
        assert!(n == index.len(), "{} != {}", n, index.len());
        (start.elapsed(), n)
    };
    println!("range-{} for ranging {} items, took {:?}", j, n, elapsed);

    let (elapsed, n) = {
        let start = time::Instant::now();
        let n: usize = index.reverse(..).map(|_| 1_usize).sum();
        assert!(n == index.len(), "{} != {}", n, index.len());
        (start.elapsed(), n)
    };
    println!(
        "reverse-{} for reverse iterating {} items, took {:?}",
        j, n, elapsed
    );
}

fn perf_omap_arc(opts: Opt, seed: u128) {
    let mut rng = SmallRng::from_seed(seed.to_le_bytes());

    let mut index: OMapArc<u64, u64> = OMapArc::new();

    // initial load
    let start = time::Instant::now();
    for _i in 0..opts.loads {
        let (key, val): (u64, u64) = (rng.gen(), rng.gen());
        index = index.set(key, val);
    }

    println!("loaded {} items in {:?}", opts.loads, start.elapsed());

    let mut handles = vec![];
    for j in 0..opts.writers {
        let (mut opts, index) = (opts.clone(), index.clone());
        opts.gets = 0;
        let seed = seed + ((j as u128) * 100);
        let h = thread::spawn(move || incr_omap_arc(j, seed, opts, index));
        handles.push(h);
    }
    for j in opts.writers..(opts.writers + opts.readers) {
        let (mut opts, index) = (opts.clone(), index.clone());
        opts.sets = 0;
        opts.dels = 0;
        let seed = seed + ((j as u128) * 100);
        let h = thread::spawn(move || incr_omap_arc(j, seed, opts, index));
        handles.push(h);
    }

    for handle in handles.into_iter() {
        handle.join().unwrap()
    }
}

fn incr_omap_arc(j: usize, seed: u128, opts: Opt, mut index: OMapArc<u64, u64>) {
    let mut rng = SmallRng::from_seed(seed.to_le_bytes());

    let start = time::Instant::now();
    let total = opts.sets + opts.dels + opts.gets;
    let mut n = total;
    while n > 0 {
        let op = rng.gen::<usize>() % total;

        let key = rng.gen::<u64>();
        if op < opts.sets {
            let val = rng.gen::<u64>();
            index = index.set(key, val);
        } else if op < (opts.sets + opts.dels) {
            index = index.remove(&key);
        } else {
            index.get(&key);
        }
        n -= 1;
    }
    println!(
        "incremental-{} for {} operations took {:?}",
        j,
        total,
        start.elapsed()
    );

    let (elapsed, n) = {
        let start = time::Instant::now();
        let n: usize = index.iter().map(|_| 1_usize).sum();
        assert!(n == index.len(), "{} != {}", n, index.len());
        (start.elapsed(), n)
    };
    println!("iter-{} for iterating {} items, took {:?}", j, n, elapsed);

    let (elapsed, n) = {
        let start = time::Instant::now();
        let n: usize = index.range(..).map(|_| 1_usize).sum();
        assert!(n == index.len(), "{} != {}", n, index.len());
        (start.elapsed(), n)
    };
    println!("range-{} for ranging {} items, took {:?}", j, n, elapsed);

    let (elapsed, n) = {
        let start = time::Instant::now();
        let n: usize = index.reverse(..).map(|_| 1_usize).sum();
        assert!(n == index.len(), "{} != {}", n, index.len());
        (start.elapsed(), n)
    };
    println!(
        "reverse-{} for reverse iterating {} items, took {:?}",
        j, n, elapsed
    );
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
