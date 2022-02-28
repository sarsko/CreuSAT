use std::fs::read_dir;

use sat::parser::parse_cnf;

#[test]
fn test_parser() {
    let mut paths = read_dir("tests/cnf/sat").unwrap();
    for path in paths {
        let tmp = path.unwrap().path();
        let path = tmp.to_str().unwrap();
        let _res = parse_cnf(path);
    }
    paths = read_dir("tests/cnf/unsat").unwrap();
    for path in paths {
        let tmp = path.unwrap().path();
        let path = tmp.to_str().unwrap();
        let _res = parse_cnf(path);
    }
}
