use no_creusot::parser::{parse_cnf, preproc_and_solve};
//use no_creusot::solver::preproc_and_solve;

use clap::{crate_authors, App, AppSettings, Arg};

//#[global_allocator]
//static GLOBAL: jemallocator::Jemalloc = jemallocator::Jemalloc;
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
    println!("c Reading file '{}'", filename);
    let res = parse_cnf(filename);
    match res {
        Ok((mut clauses, num_literals)) => {
            println!("c Parsed formula with {} clauses and {} literals", clauses.len(), num_literals);
            let result = preproc_and_solve(&mut clauses, num_literals);

            if result {
                println!("c SAT");
            } else {
                println!("c UNSAT");
            }
        },
        Err(e) => {
            println!("c Parser errored with message: {}", e);
        }
    }
}