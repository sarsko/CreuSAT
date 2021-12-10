use std::fs::read_dir;

use no_creusot::parser::parse_cnf;
use no_creusot::solver::preproc_and_solve;

#[test]
fn test_all_sat() {
    let paths = read_dir("../tests/cnf/sat").unwrap();
    for path in paths {
        let (mut clauses, num_literals) = parse_cnf(path.unwrap().path().to_str().unwrap());
        let result = preproc_and_solve(&mut clauses, num_literals);
        assert!(result);
    }
}

#[test]
fn test_all_unsat() {
    let paths = read_dir("../tests/cnf/unsat").unwrap();
    for path in paths {
        let (mut clauses, num_literals) = parse_cnf(path.unwrap().path().to_str().unwrap());
        let result = preproc_and_solve(&mut clauses, num_literals);
        assert!(!result);
    }
}
