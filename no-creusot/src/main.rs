use no_creusot::parser::parse_cnf;
use no_creusot::solver::preproc_and_solve;
//use sat::solver::dpll;

use clap::{crate_authors, App, AppSettings, Arg};


fn main() {
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

    if result {
        println!("Sat");
    } else {
        println!("Unsat");
    }
}
