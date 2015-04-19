#![feature(test)]
#![feature(collections)]
#![feature(alloc)]
#![feature(box_patterns)]

#[cfg(test)]
extern crate test;

#[cfg(test)]
extern crate rand;

#[cfg(test)]
#[macro_use]
mod bench_macros;

mod map;
pub use map::*;
