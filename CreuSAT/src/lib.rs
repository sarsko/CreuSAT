#![feature(type_ascription)]
#![cfg_attr(not(feature = "contracts"), feature(stmt_expr_attributes, proc_macro_hygiene))]
#![allow(unused_imports)]
#![allow(unused)]
#![allow(dead_code)]
#![allow(non_snake_case)]
#![recursion_limit = "512"]
extern crate creusot_contracts;

use creusot_contracts::logic::Ghost;
use creusot_contracts::std::*;
use creusot_contracts::*;

mod assignments;
mod clause;
mod conflict_analysis;
mod decision;
mod formula;
mod lit;
mod logic;
pub mod parser;
mod target_phase;
mod solver;
mod trail;
mod unit_prop;
mod util;
mod watches;
