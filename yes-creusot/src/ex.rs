extern crate creusot_contracts;

use creusot_contracts::*;
use creusot_contracts::std::*;

/*
fn err() {
    let a = 0;
    match a {
        0..=8 => {},
        0..=8 => {}
    }
}
*/

fn err() {
    let a = 0;
    match a {
        _ => {},
        _ => {}
    }
}

/*
fn err() {
    let a = 0;
    match a {
        0..=8 => {},
        0..=8 => {}
    }
}
*/

/*:
fn err() {
    let zero = 0;
    let ref_zero = &zero;
    let a = &zero;
    match a {
        &zero => {},
        ref_zero => {}
    }
}
*/

fn no_err() {
    let a = 0;
    match a {
        0..=8 => {},
        0..=7 => {}
    }
}

/*

fn ex() {
    let a = 0;
    match a {
        0 | 1 => {}
        2 => {}
    }
}

fn ex2() {
    let a = 0;
    match a {
        0 | 1 => {}
        1 | 2 => {}
    }
}
*/


/*
fn ex() {
    let a = 0;
    match a {
        _ => {}
        0 => {}
    }
}
*/