#![feature(box_patterns)]
#![feature(asm)]
#![cfg_attr(test, feature(test))]
//
// #![feature(alloc_system)]
//
// extern crate alloc_system;

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

mod map;
pub use map::*;
