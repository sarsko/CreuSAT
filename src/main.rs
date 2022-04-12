//use no_creusot::solver::preproc_and_solve;


#[cfg(feature = "contracts")]
fn main() {}

//#[global_allocator]
//static GLOBAL: jemallocator::Jemalloc = jemallocator::Jemalloc;
#[cfg(not(feature = "contracts"))]
fn main() {
    use clap::{crate_authors, App, AppSettings, Arg};
    use sat::parser::{parse_cnf, preproc_and_solve};
    let matches = App::new("\nA minimal SAT solver with no name")
        .author(crate_authors!("\n"))
        .about("A verified SAT solver written in Rust.")
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