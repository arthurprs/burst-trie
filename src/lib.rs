#![feature(box_patterns)]
#![feature(unsafe_no_drop_flag)]
#![feature(asm)]
#![feature(test)]

extern crate crossbeam;
extern crate spin;
extern crate arrayvec;
#[macro_use]
extern crate lazy_static;

#[cfg(test)]
extern crate test;

#[cfg(test)]
extern crate rand;

#[cfg(test)]
#[macro_use]
mod bench_macros;

// mod permutation;

mod map;
pub use map::*;
