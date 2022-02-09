#![recursion_limit = "256"]
extern crate creusot_contracts;

use creusot_contracts::*;
use creusot_contracts::std::*;
//pub mod parser;
//pub mod types;
pub mod solver;

pub mod assignments;
pub mod clause;
pub mod conflict_analysis;
pub mod formula;
pub mod lit;
pub mod trail;
pub mod watches;