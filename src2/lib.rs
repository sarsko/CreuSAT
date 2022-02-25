#![feature(type_ascription)]
#![feature(stmt_expr_attributes)]
#![allow(unused_imports)]
#![recursion_limit = "256"]
extern crate creusot_contracts;

use creusot_contracts::*;
use creusot_contracts::std::*;

pub mod lit;
pub mod clause;
pub mod assignments;
pub mod formula;
pub mod logic;
pub mod solver_dpll;