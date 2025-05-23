//#![feature(type_ascription)]
#![allow(non_snake_case)]
//#![cfg_attr(not(creusot), feature(stmt_expr_attributes, proc_macro_hygiene))]
#![allow(unused)]

#[allow(unused)]
use creusot_contracts::std::*;
#[allow(unused)]
use creusot_contracts::*;

mod assignments;
mod clause;
mod decision;
mod formula;
mod lit;
pub mod parser;
mod solver;
mod util;

#[cfg(creusot)]
mod logic;
