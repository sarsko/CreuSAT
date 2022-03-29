extern crate creusot_contracts;
use creusot_contracts::*;

#[logic]
pub fn ex() -> bool { true }

#[ensures(ex)]
pub fn main() {
    //#[invariant(inv, ex)]
    while true {}
}