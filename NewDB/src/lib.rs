#![allow(non_snake_case)]
#![allow(unused)]
#![feature(type_ascription)]
#![cfg_attr(not(creusot), feature(stmt_expr_attributes, proc_macro_hygiene))]
extern crate creusot_contracts;

use creusot_contracts::logic::FSet;
use creusot_contracts::{std::clone::Clone, std::*, vec, *};

mod assignments;
mod friday;
mod lit;
mod logic_util;
mod formula;
mod clause_allocator;
mod clause_manager;
mod cref_manager;
mod clause;


