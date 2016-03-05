
pub static BENCH_SEED: &'static[usize] = &[0, 1, 1, 2, 3, 5, 8, 13, 21, 34];

macro_rules! map_get_rnd_bench {
    ($name: ident, $min_len: expr, $max_len: expr, $map_len: expr, $map_type: ident, $key_prefix: expr) => (
        #[bench]
        #[allow(unused_mut)]
        fn $name(b: &mut test::Bencher) {
            use rand::{Rng, StdRng, SeedableRng};

            let mut rng: StdRng = SeedableRng::from_seed(BENCH_SEED);
            let mut map = $map_type::new();
            let value = 0usize; 

            let keys = (0..$map_len).map(|_| {
                let key_len = rng.gen_range($min_len, $max_len);
                $key_prefix.to_string() + rng.gen_ascii_chars().take(key_len).collect::<String>().as_ref()
            }).collect::<Vec<_>>();

            for key in &keys {
                map.insert(key.clone(), value);
            }

            b.iter(|| {
                let key = rng.choose(&keys).unwrap();
                test::black_box(map.get(key));
            });

            test::black_box(map);
        }
    );
    ($name: ident, $min_len: expr, $max_len: expr, $map_len: expr, $map_type: ident) => (
        map_get_rnd_bench!($name, $min_len, $max_len, $map_len, $map_type, "");
    );
}

macro_rules! map_insert_rnd_bench {
    ($name: ident, $min_len: expr, $max_len: expr, $map_len: expr, $map_type: ident, $key_prefix: expr) => (
        #[bench]
        #[allow(unused_mut)]
        fn $name(b: &mut test::Bencher) {
            use rand::{Rng, StdRng, SeedableRng};

            let mut rng: StdRng = SeedableRng::from_seed(BENCH_SEED);
            let mut map = $map_type::new();
            let value = 0usize; 

            let keys = (0..$map_len).map(|_| {
                let key_len = rng.gen_range($min_len, $max_len);
                $key_prefix.to_string() + rng.gen_ascii_chars().take(key_len).collect::<String>().as_ref()
            }).collect::<Vec<_>>();
            
            b.iter(|| {
                let key = rng.choose(&keys).unwrap();
                map.insert(key.clone(), value);
            });

            test::black_box(map);
        }
    );
    ($name: ident, $min_len: expr, $max_len: expr, $map_len: expr, $map_type: ident) => (
        map_insert_rnd_bench!($name, $min_len, $max_len, $map_len, $map_type, "");
    );
}

macro_rules! map_get_seq_bench {
    ($name: ident, $min_len: expr, $max_len: expr, $map_len: expr, $map_type: ident, $key_prefix: expr) => (
        #[bench]
        #[allow(unused_mut)]
        fn $name(b: &mut test::Bencher) {
            use rand::{Rng, StdRng, SeedableRng};

            let mut rng: StdRng = SeedableRng::from_seed(BENCH_SEED);
            let mut map = $map_type::new();
            let value = 0usize;

            let start_num: u64 = "100000000000000000000000000000000000"[..$min_len].parse().unwrap();

            let keys = (0..$map_len).map(|i| {
                let key_len = rng.gen_range(0, $max_len - $min_len);
                $key_prefix.to_string() + (start_num + i).to_string().as_ref() + rng.gen_ascii_chars().take(key_len).collect::<String>().as_ref()
            }).collect::<Vec<_>>();

            for key in &keys {
                map.insert(key.clone(), value);
            }

            let mut i = 0;
            b.iter(|| {
                test::black_box(map.get(&keys[i % keys.len()]));
                i += 1;
            });

            test::black_box(map);
        }
    );
    ($name: ident, $min_len: expr, $max_len: expr, $map_len: expr, $map_type: ident) => (
        map_get_seq_bench!($name, $min_len, $max_len, $map_len, $map_type, "");
    );
}

macro_rules! map_insert_seq_bench {
    ($name: ident, $min_len: expr, $max_len: expr, $map_len: expr, $map_type: ident, $key_prefix: expr) => (
        #[bench]
        #[allow(unused_mut)]
        fn $name(b: &mut test::Bencher) {
            use rand::{Rng, StdRng, SeedableRng};

            let mut rng: StdRng = SeedableRng::from_seed(BENCH_SEED);
            let mut map = $map_type::new();
            let value = 0usize; 

            let start_num: u64 = "100000000000000000000000000000000000"[..$min_len].parse().unwrap();

            let keys = (0..$map_len).map(|i| {
                let key_len = rng.gen_range(0, $max_len - $min_len);
                $key_prefix.to_string() + (start_num + i).to_string().as_ref() + rng.gen_ascii_chars().take(key_len).collect::<String>().as_ref()
            }).collect::<Vec<_>>();
            
            let mut i = 0;
            b.iter(|| {
                map.insert(keys[i % keys.len()].clone(), value);
                i += 1;
            });

            test::black_box(map);
        }
    );
    ($name: ident, $min_len: expr, $max_len: expr, $map_len: expr, $map_type: ident) => (
        map_insert_seq_bench!($name, $min_len, $max_len, $map_len, $map_type, "");
    );
}

macro_rules! map_iter_bench {
    ($name: ident, $min_len: expr, $max_len: expr, $map_len: expr, $map_type: ident, $key_prefix: expr) => (
        #[bench]
        #[allow(unused_mut)]
        fn $name(b: &mut test::Bencher) {
            use rand::{Rng, StdRng, SeedableRng};

            let mut rng: StdRng = SeedableRng::from_seed(BENCH_SEED);
            let mut map = $map_type::new();
            let value = 0usize; 

            (0..$map_len).map(|_| {
                let key_len = rng.gen_range($min_len, $max_len);
                let key = $key_prefix.to_string() + rng.gen_ascii_chars().take(key_len).collect::<String>().as_ref();
                map.insert(key, value);
            }).count();
            
            b.iter(|| {
                for (key, value) in map.iter() {
                    test::black_box(key);
                    test::black_box(value);
                }
            });
        }
    );
    ($name: ident, $min_len: expr, $max_len: expr, $map_len: expr, $map_type: ident) => (
        map_iter_bench!($name, $min_len, $max_len, $map_len, $map_type, "");
    );
}

macro_rules! map_range_bench {
    ($name: ident, $min_len: expr, $max_len: expr, $map_len: expr, $map_type: ident, $key_prefix: expr) => (
        #[bench]
        #[allow(unused_mut)]
        fn $name(b: &mut test::Bencher) {
            use rand::{Rng, StdRng, SeedableRng};
            use std::collections::Bound;

            let mut rng: StdRng = SeedableRng::from_seed(BENCH_SEED);
            let mut map = $map_type::new();
            let value = 0usize;

            (0..$map_len).map(|_| {
                let key_len = rng.gen_range($min_len, $max_len);
                let key = $key_prefix.to_string() + rng.gen_ascii_chars().take(key_len).collect::<String>().as_ref();
                map.insert(key.clone(), value);
                key
            }).count();

            let keys = map.keys().collect::<Vec<_>>();

            b.iter(|| {
                let min = Bound::Included(keys[keys.len() / 4]);
                let max = Bound::Excluded(keys[keys.len() - keys.len() / 4]);
                for (key, value) in map.range(min, max) {
                    test::black_box(key);
                    test::black_box(value);
                }
            });
        }
    );
    ($name: ident, $min_len: expr, $max_len: expr, $map_len: expr, $map_type: ident) => (
        map_range_bench!($name, $min_len, $max_len, $map_len, $map_type, "");
    );
}
