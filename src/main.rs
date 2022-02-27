#![feature(type_ascription)]

//extern crate creusot_contracts;

//use creusot_contracts::std::*;
//use creusot_contracts::*;

//use sat::parser::parse_cnf;
//use sat::solver::dpll;

//use clap::{crate_authors, App, AppSettings, Arg};

//use sat::solver_dpll_noproofs::preproc_and_solve;

//#[trusted]
fn main() {
    /*
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
                .help("CNF file to be parsed"),
        )
        .get_matches();
    let filename = matches.value_of("file").unwrap();
    let (mut clauses, num_literals) = parse_cnf(filename);
    println!("Parse complete");
    let result = preproc_and_solve(&mut clauses, num_literals);

    /*
    let result = dpll(&mut clauses, 1, num_literals);
    */
    if result {
        println!("Sat");
    } else {
        println!("Unsat");
    }
    */
}
