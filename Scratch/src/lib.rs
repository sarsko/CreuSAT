#![feature(type_ascription)]
#![cfg_attr(not(creusot), feature(stmt_expr_attributes, proc_macro_hygiene))]
#![allow(unused_imports)]
#![allow(unused)]
#![allow(dead_code)]
#![allow(non_snake_case)]
mod assignments;
mod clause;
mod formula;
mod lit;
mod scratch;
mod restart;
mod vsids;

#[cfg(creusot)]
mod logic;
