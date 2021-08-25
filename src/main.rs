use sat::parser::parse_cnf;
use sat::solver::dpll;

use clap::{crate_authors, App, AppSettings, Arg};


fn main() {
    /*
    let mut clauses = parse_cnf("cnfs/uf8.cnf");
    let mut clauses = parse_cnf("cnfs/empty-clause.cnf");
    let mut clauses = parse_cnf("cnfs/unsat.cnf");
    let mut clauses = parse_cnf("cnfs/uf20-01.cnf");
    let mut clauses = parse_cnf("cnfs/unsat-ex01.cnf");
    let mut clauses = parse_cnf("cnfs/uf250-02.cnf");
    */
    let matches = App::new("\nA minimal SAT solver with no name")
        .author(crate_authors!("\n"))
        .about("A yet unverified SAT solver written in Rust.")
        .usage("cargo run -- [FLAGS] --file <file>")
        .setting(AppSettings::ColoredHelp)
        .setting(AppSettings::DisableVersion)
        .arg(
            Arg::with_name("file")
                .short("f")
                .long("file")
                .takes_value(true)
                .required(true)
                .help("Program file to be parsed"),
        )
        .get_matches();
    let filename = matches.value_of("file").unwrap();
    let mut clauses = parse_cnf(filename);
    println!("Parse complete");
    let result = dpll(&mut clauses, 1);
    if result {
        println!("Sat");
    } else {
        println!("Unsat");
    }
}
