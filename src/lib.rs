#![feature(type_ascription)]
#![feature(stmt_expr_attributes)]
#![feature(proc_macro_hygiene)]
#![allow(unused_imports)]
#![recursion_limit = "512"]
extern crate creusot_contracts;

use creusot_contracts::*;
use creusot_contracts::std::*;

pub mod lit;
pub mod clause;
pub mod assignments;
pub mod formula;
pub mod logic;
pub mod solver_dpll;
pub mod parser;
pub mod util;
pub mod decision;
pub mod trail;
pub mod watches;
pub mod conflict_analysis;
pub mod unit_prop;
mod ntrail;
mod logic_ntrail;