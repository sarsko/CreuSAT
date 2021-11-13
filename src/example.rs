#![feature(type_ascription)]

extern crate creusot_contracts;

use creusot_contracts::std::*;
use creusot_contracts::*;

fn main() {}


fn ex() {
    let mut i = 0;
    #[invariant(li, 0 <= @i && @i <= 10)]
    while i < 10 {
        i += 1;
    }
}

