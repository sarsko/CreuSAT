use crate::parser::parse_cnf;
use crate::solver::dpll;

mod parser;
mod types;
mod solver;
mod test;

fn main() {
    /*
    let mut clauses = parse_cnf("cnfs/uf8.cnf");
    let mut clauses = parse_cnf("cnfs/empty-clause.cnf");
    let mut clauses = parse_cnf("cnfs/unsat.cnf");
    let mut clauses = parse_cnf("cnfs/uf20-01.cnf");
    let mut clauses = parse_cnf("cnfs/unsat-ex01.cnf");
    let mut clauses = parse_cnf("cnfs/uf250-02.cnf");
    */
    let mut clauses = parse_cnf("cnfs/uf100-010.cnf");
    println!("Parse complete");
    let result = dpll(&mut clauses, 1);
    if result {
        println!("Sat");
    } else {
        println!("Unsat");
    }
}
