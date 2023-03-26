extern crate creusot_contracts;

use creusot_contracts::*;

#[logic]
#[why3::attr = "inline:trivial"]
pub(crate) fn bool_as_u8(b: bool) -> u8 {
    pearlite! {
       match b {
           true => 1u8,
           false => 0u8,
       }
    }
}
