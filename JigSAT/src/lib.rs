#![feature(type_ascription)]
#![allow(non_snake_case)]
#![feature(generic_associated_types)]

mod assignments;
mod clause;
mod clause_database;
mod conflict_analysis;
mod decision;
mod formula;
mod lit;
mod minimize;
mod modes;
pub mod parser;
mod preprocess;
mod restart;
mod solver;
mod solver_types;
mod target_phase;
mod trail;
mod unit_prop;
mod util;
mod watches;
