extern crate creusot_contracts;
use creusot_contracts::*;
#[ensures(result == (@a < @b))] 
fn compare(a: u32, b: usize) -> bool {
    (a as usize) < b
}