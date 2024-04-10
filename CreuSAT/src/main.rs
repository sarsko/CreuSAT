use clap::{arg, crate_authors, Command};

#[cfg(creusot)]
fn main() {}

#[cfg(not(creusot))]
fn main() {
    use CreuSAT::parser::{parse_cnf, preproc_and_solve};
    let matches = Command::new("\nCreuSAT")
        .author(crate_authors!("\n"))
        .about("A verified SAT solver written in Rust.")
        .disable_colored_help(false)
        .disable_version_flag(true)
        .arg(arg!(-f --file <FILENAME>).long("file").required(true).help("CNF file to be parsed"))
        .get_matches();
    let filename = matches.get_one::<String>("file").unwrap();
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
