#![feature(type_ascription)]
#![cfg_attr(not(feature = "contracts"), feature(stmt_expr_attributes, proc_macro_hygiene))]
#![allow(unused_imports)]
#![allow(unused)]
#![allow(dead_code)]
#![recursion_limit = "256"]
extern crate creusot_contracts;

use creusot_contracts::std::*;
use creusot_contracts::*;

pub mod assignments;
pub mod clause;
pub mod decision;
pub mod formula;
pub mod lit;
pub mod logic;
pub mod parser;
pub mod solver;
pub mod util;
