#![feature(type_ascription)]
#![feature(stmt_expr_attributes)]
#![feature(proc_macro_hygiene)]
#![allow(unused_imports)]
#![allow(non_snake_case)]
#![allow(dead_code)]
#![allow(unused_must_use)]
#![allow(unused_variables)]
#![allow(unused_mut)]
#![recursion_limit = "512"]
extern crate creusot_contracts;

use creusot_contracts::*;
use creusot_contracts::std::*;

mod assignments;
mod clause;
mod conflict_analysis;
mod decision;
mod formula;
mod lit;
mod logic;
pub mod parser;
mod solver;
mod trail;
mod unit_prop;
mod util;
mod watches;