//#![feature(type_ascription)]
extern crate creusot_contracts;
use creusot_contracts::*;
#[requires(*x < u32::MAX)]
//#[ensures(^x == *x + 1u32)]
pub fn incr(x: &mut u32) { *x += 1 }

pub fn main() {
    //let mut var: u32 = 0;
    //incr(&mut var);
}
