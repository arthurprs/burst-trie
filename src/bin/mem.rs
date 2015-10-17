#![feature(alloc)]
#![feature(libc)]

extern crate rand;
extern crate burst_trie;
extern crate libc;

use std::cmp::max;
use std::io::Read;
use std::io;
use std::thread;
use std::default::Default;
use burst_trie::BurstTrieMap;
use std::collections::{HashMap, BTreeMap};
use std::ascii::AsciiExt;
use libc::*;

extern {fn je_malloc_stats_print (write_cb: extern fn (*const c_void, *const c_char), cbopaque: *const c_void, opts: *const c_char);}
extern fn write_cb (_: *const c_void, message: *const c_char) {
    print! ("{}", String::from_utf8_lossy (unsafe {std::ffi::CStr::from_ptr (message as *const i8) .to_bytes()}));
}

fn stats_print() {
    unsafe {je_malloc_stats_print (write_cb, std::ptr::null(), std::ptr::null())};
}

fn main() {
    let words = gen_words(10000, 3, 25);
    // let words = read_words();
    println!("--sample--\n{:#?}--", &words[..10]);
    let mut word_counts: HashMap<String, usize> = Default::default();
    for word in words {
        let len = word.len();
        word_counts.insert(word, len);
    }
    stats_print();

    // word_counts.print_structure();
}

fn read_words() -> Vec<String> {
    let mut input = String::new();
    io::stdin().read_to_string(&mut input).unwrap();
    input.split_whitespace()
        .map(|w| w.trim_matches(|c| ['.', '"', ':', ';', ',', '!', '?', ')', '(', '_']
                  .contains(&c)))
        .map(|w| w.to_lowercase())
        .filter(|w| !w.is_empty())
        .collect()
}

fn gen_words(count: usize, min_len: usize, max_len: usize) -> Vec<String> {
    use rand::{Rng, StdRng, SeedableRng};
    static SEED: &'static[usize] = &[0, 1, 1, 2, 3, 5, 8, 13, 21, 34];
    let mut rng: StdRng = SeedableRng::from_seed(SEED);
    (0..count).map(|_| {
        let key_len = rng.gen_range(min_len, max_len);
        rng.gen_ascii_chars().take(key_len).collect::<String>()
    }).collect()
}