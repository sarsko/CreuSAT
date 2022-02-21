use std::fs::read_dir;
use std::io::Write;
use std::time::Instant;
use termcolor::*;

use no_creusot::parser::{parse_cnf, preproc_and_solve};
//use no_creusot::solver::preproc_and_solve;

#[test]
fn test_all_sat() {
    test_all_path("../tests/cnf/sat", true, 500);
}

#[test]
fn test_all_unsat() {
    test_all_path("../tests/cnf/unsat", false, 500);
}

// paths: Path to directory to be read, 
// excpected: expected value for the assertion,
// veboristy: 0 for no prints, else every nth test will result in a print
fn test_all_path(paths_in: &str, expected: bool, verbosity: usize) {
    let paths = read_dir(paths_in).unwrap();
    let mut out = StandardStream::stdout(ColorChoice::Always);
    out.set_color(ColorSpec::new().set_fg(Some(Color::Green))).ok();
    let mut i = 0;
    let mut start = Instant::now();
    for path in paths {
        let tmp = path.unwrap().path();
        let path = tmp.to_str().unwrap();
        let res = parse_cnf(path);
        match res {
            Ok((mut clauses, num_literals)) => {
                let result = preproc_and_solve(&mut clauses, num_literals);
                assert!(result == expected);
            },
            Err(e) => {
                panic!("Parser errored with message: {}", e);
            }
        }
        i += 1;
        if verbosity > 0 {
            let elapsed = start.elapsed();
            if i % verbosity == 0 {
                writeln!(&mut out, "First {:>4} tests in {} OK. Duration: {} secs", i, paths_in, elapsed.as_secs_f64()).ok();
            }
        }
    }
    let elapsed = start.elapsed();
    writeln!(&mut out, "All {:>6} tests in {} OK. Total duration: {} secs", i, paths_in, elapsed.as_secs_f64()).ok();
}

#[test]
fn test_all_uf100() {
    test_all_path("tests/satlib/UF100.430.1000", true, 100);
}

#[test]
fn test_all_uuf100() {
    test_all_path("tests/satlib/UUF100.430.1000", false, 100);
}

#[test]
fn test_all_uf125() {
    test_all_path("tests/satlib/UF125.538.100", true, 20);
}

#[test]
fn test_all_uuf125() {
    test_all_path("tests/satlib/UUF125.538.100", false, 20);
}

#[test]
fn test_all_uf150() {
    test_all_path("tests/satlib/UF150.645.100", true, 1);
}

#[test]
fn test_all_uuf150() {
    test_all_path("tests/satlib/UUF150.645.100", false, 1);
}

#[test]
fn test_all_uf175() {
    test_all_path("tests/satlib/UF175.753.100", true, 1);
}

#[test]
fn test_all_uuf175() {
    test_all_path("tests/satlib/UUF175.753.100", false, 1);
}

#[test]
fn test_all_uf200() {
    test_all_path("tests/satlib/UF200.860.100", true, 1);
}

#[test]
fn test_all_uuf200() {
    test_all_path("tests/satlib/UUF200.860.100", false, 1);
}

#[test]
fn test_all_uf225() {
    test_all_path("tests/satlib/UF225.960.100", true, 1);
}

#[test]
fn test_all_uuf225() {
    test_all_path("tests/satlib/UUF225.960.100", false, 1);
}

#[test]
fn test_all_uf250() {
    test_all_path("tests/satlib/UF250.1065.100", true, 1);
}

#[test]
fn test_all_uuf250() {
    test_all_path("tests/satlib/UUF250.1065.100", false, 1);
}