use std::fs::read_dir;

use no_creusot::parser::parse_cnf;

#[test]
fn test_parser() {
    let mut paths = read_dir("../tests/cnf/sat").unwrap();
    for path in paths {
        let (mut _clauses, _num_literals) = parse_cnf(path.unwrap().path().to_str().unwrap());
    }
    paths = read_dir("../tests/cnf/unsat").unwrap();
    for path in paths {
        let (mut _clauses, _num_literals) = parse_cnf(path.unwrap().path().to_str().unwrap());
    }
}
