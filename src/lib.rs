#![feature(core)]
#![feature(collections)]
#![feature(test)]
#![feature(alloc)]

extern crate collections;
extern crate rand;
#[cfg(test)]
extern crate test;

#[cfg(test)]
#[macro_use]
mod bench_macros;
pub mod map;

pub use map::*;
