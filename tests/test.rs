use std::fs::read_dir;

use sat::parser::parse_cnf;
use sat::solver::dpll;

#[test]
fn test_all_sat() {
    let paths = read_dir("tests/cnf/sat").unwrap();
    let mut numtests = 200;
    for path in paths {
        let (mut clauses, num_literals) = parse_cnf(path.unwrap().path().to_str().unwrap());
        let result = dpll(&mut clauses, 1, num_literals);
        assert!(result);
        numtests -= 1;
        if numtests <= 0 {
            break;
        }
    }
}

#[test]
fn test_all_unsat() {
    let paths = read_dir("tests/cnf/unsat").unwrap();
    let mut numtests = 200;
    for path in paths {
        let (mut clauses, num_literals) = parse_cnf(path.unwrap().path().to_str().unwrap());
        let result = dpll(&mut clauses, 1, num_literals);
        assert!(!result);
        numtests -= 1;
        if numtests <= 0 {
            break;
        }
    }
}