#![feature(test)]
#![feature(box_patterns)]
#![feature(collections_bound)]
#![feature(btree_range)]
#![feature(slice_extras)]
#![feature(unsafe_no_drop_flag)]
#![feature(asm)]

#[cfg(test)]
extern crate test;

#[cfg(test)]
extern crate rand;

#[cfg(test)]
#[macro_use]
mod bench_macros;

mod map;
pub use map::*;
