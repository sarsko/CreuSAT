use clap::{crate_authors, App, AppSettings, Arg};

fn main() {
    use JigSAT::parser::{parse_cnf, preproc_and_solve};
    let matches = App::new("\nJigSAT")
        .author(crate_authors!("\n"))
        .about("A non-verified SAT solver which acts as a playground for CreuSAT.")
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
