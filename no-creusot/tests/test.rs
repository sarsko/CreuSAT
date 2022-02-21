use std::fs::read_dir;
//use std::io::{BufRead, BufReader, Write};
//use termcolor::*;

use no_creusot::parser::{parse_cnf, preproc_and_solve};
//use no_creusot::solver::preproc_and_solve;

#[test]
fn test_all_sat() {
    let paths = read_dir("../tests/cnf/sat").unwrap();
    for path in paths {
        let tmp = path.unwrap().path();
        let path = tmp.to_str().unwrap();
        let res = parse_cnf(path);
        match res {
            Ok((mut clauses, num_literals)) => {
                let result = preproc_and_solve(&mut clauses, num_literals);
                assert!(result);
            },
            Err(e) => {
                panic!("Parser errored with message: {}", e);
            }
        }
        //let mut out = StandardStream::stdout(ColorChoice::Always);
        //write!(&mut out, "Testing sat ...");
    }
}

#[test]
fn test_all_unsat() {
    let paths = read_dir("../tests/cnf/unsat").unwrap();
    for path in paths {
        let tmp = path.unwrap().path();
        let path = tmp.to_str().unwrap();
        let res = parse_cnf(path);
        match res {
            Ok((mut clauses, num_literals)) => {
                let result = preproc_and_solve(&mut clauses, num_literals);
                assert!(!result);
            },
            Err(e) => {
                panic!("Parser errored with message: {}", e);
            }
        }
        //let mut out = StandardStream::stdout(ColorChoice::Always);
        //write!(&mut out, "Testing sat ...");
    }
}
