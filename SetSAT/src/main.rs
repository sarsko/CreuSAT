use clap::{crate_authors, App, AppSettings, Arg};

#[cfg(feature = "contracts")]
fn main() {}

#[cfg(not(feature = "contracts"))]
fn main() {
    use SetSAT::{
        parser::parse_cnf,
        solver::{solve, SatResult},
    };
    let matches = App::new("\nSetSAT")
        .author(crate_authors!("\n"))
        .about("A minimal CDCL SAT solver.")
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
        Ok(clause_db) => {
            let result = solve(clause_db);

            match result {
                SatResult::Sat => println!("s SATISFIABLE"),
                SatResult::Unsat => println!("s UNSATISFIABLE"),
                SatResult::Unknown => panic!("c Impossible"),
            }
        }
        Err(e) => {
            println!("c Parser errored with message: {}", e);
        }
    }
}
