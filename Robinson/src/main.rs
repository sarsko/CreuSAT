//#[global_allocator]
//static GLOBAL: jemallocator::Jemalloc = jemallocator::Jemalloc;

#[cfg(feature = "contracts")]
fn main() {}

#[cfg(not(feature = "contracts"))]
fn main() {
    use clap::{crate_authors, App, AppSettings, Arg};
    use Robinson::parser::{parse_cnf, preproc_and_solve};
    let matches = App::new("\nRobinson")
        .author(crate_authors!("\n"))
        .about("A verified DPLL-based SAT solver written in Rust.")
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
                println!("s SATISFIABLE");
            } else {
                println!("s UNSATISFIABLE");
            }
        }
        Err(e) => {
            println!("c Parser errored with message: {}", e);
        }
    }
}
