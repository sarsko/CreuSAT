use std::fs::read_dir;
use std::io::Write;
use std::time::Instant;
use termcolor::*;

use sat::parser::parse_cnf;
use sat::parser::preproc_and_solve;
//use sat::solver_dpll::dpll;
//use sat::solver_dpll_noproofs::preproc_and_solve;

//#[cfg(no_contracts)]
#[test]
fn test_all_sat() {
    test_all_path("tests/cnf/sat", true, 500);
}

//#[cfg(no_contracts)]
#[test]
fn test_all_unsat() {
    test_all_path("tests/cnf/unsat", false, 500);
}

// paths: Path to directory to be read, 
// expected: expected value for the assertion,
// verbosity: 0 for no prints, else every nth test will result in a print
//#[cfg(no_contracts)]
fn test_all_path(paths_in: &str, expected: bool, verbosity: usize) {
    let paths = read_dir(paths_in).unwrap();
    let mut out = StandardStream::stdout(ColorChoice::Always);
    out.set_color(ColorSpec::new().set_fg(Some(Color::Green))).ok();
    let mut i = 0;
    let start = Instant::now();
    for path in paths {
        let tmp = path.unwrap().path();
        let path = tmp.to_str().unwrap();
        let res = parse_cnf(path);
        //writeln!(&mut out, "parse ok").ok();
        match res {
            Ok((mut clauses, num_literals)) => {
                let result = preproc_and_solve(&mut clauses, num_literals);
                //writeln!(&mut out, "Result = {}", result).ok();
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