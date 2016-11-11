#![cfg_attr(test, feature(test))]
#![feature(box_patterns)]
#![cfg_attr(test, feature(collections_bound))]
#![cfg_attr(test, feature(btree_range))]
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
