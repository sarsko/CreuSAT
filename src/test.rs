use std::fs::read_dir;

use crate::parser::parse_cnf;
use crate::solver::dpll;
use crate::types::*;


#[test]
fn test_all_sat() {
    let paths = read_dir("tests/cnf/sat").unwrap();
    let mut numtests = 20;
    for path in paths {
        let mut clauses = parse_cnf(path.unwrap().path().to_str().unwrap());
        let result = dpll(&mut clauses, 1);
        assert!(result);
        numtests -= 1;
        if numtests == 0 {
            break;
        }
    }
}

#[test]
fn test_all_unsat() {
    let paths = read_dir("tests/cnf/unsat").unwrap();
    let mut numtests = 5;
    for path in paths {
        let mut clauses = parse_cnf(path.unwrap().path().to_str().unwrap());
        let result = dpll(&mut clauses, 1);
        assert!(!result);
        numtests -= 1;
        if numtests == 0 {
            break;
        }
    }
}
