use std::fs::File;
use std::io::{self, BufRead};
use std::path::Path;

use crate::clause::Clause as Clause2;
use crate::formula::*;
use crate::lit::Lit as Lit2;
use crate::solver::*;

pub type Literal = i32;
pub type Clause = Vec<Literal>;
pub type Clauses = Vec<Clause>;

#[cfg(not(feature = "contracts"))]
fn read_lines<P>(filename: P) -> io::Result<io::Lines<io::BufReader<File>>>
where
    P: AsRef<Path>,
{
    let file = File::open(filename)?;
    Ok(io::BufReader::new(file).lines())
}
#[cfg(not(feature = "contracts"))]
pub fn parse_cnf(infile: &str) -> Result<(Clauses, usize), String> {
    /*
    let mut problem_type = "";
    let mut num_clauses = 0;
    */
    use std::collections::HashSet;
    let mut num_literals = 0;
    let mut num_lits_set = false;
    let mut out_clauses = vec![];
    let mut curr_clause = vec![];
    let mut line_cntr = 0;
    let mut max_literal: usize = 0;
    if let Ok(lines) = read_lines(infile) {
        for line in lines {
            line_cntr += 1;
            if let Ok(line) = line {
                let split = line.split(' ').filter(|e| e != &"").collect::<Vec<_>>();
                if split.len() > 0 {
                    match split[0].chars().next().unwrap() {
                        'c' => {}
                        'p' => match split[2].parse::<usize>() {
                            Ok(n) => {
                                if num_lits_set {
                                    return Err("Error in input file - multiple p lines".to_string());
                                }
                                num_lits_set = true;
                                num_literals = n
                            }
                            Err(_) => {
                                return Err("Error in input file".to_string());
                            }
                        },
                        '%' => {
                            break;
                        } // The Satlib files follow this convention
                        _ => {
                            let mut seen = HashSet::new();
                            for e in split {
                                match e.parse::<i32>() {
                                    Ok(n) => {
                                        if n == 0 {
                                            out_clauses.push(curr_clause);
                                            curr_clause = vec![];
                                        } else {
                                            let n_abs = n.unsigned_abs() as usize;
                                            if n_abs > max_literal {
                                                max_literal = n_abs;
                                            }
                                            if !seen.contains(&n) {
                                                curr_clause.push(n);
                                                seen.insert(n);
                                            }
                                        }
                                    }
                                    Err(_) => {
                                        return Err(format!("Error in input file on line {}", line_cntr));
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }
    } else {
        return Err("File not found!".to_string());
    }
    if !num_lits_set {
        //return Err("Error in input file - no p line".to_string());
    }
    if num_literals != max_literal {
        //return Err("p line does not match the actual number of literals".to_string());
        num_literals = max_literal;
    }
    if curr_clause.len() > 0 {
        return Err("Error in input file - last clause not terminated".to_string());
    }
    Ok((out_clauses, num_literals))
}

#[cfg(not(feature = "contracts"))]
// TODO, fix it so that 0 and 1 len clauses are supported
/// Takes a 1-indexed 2d vector and converts it to a 0-indexed formula
pub fn preproc_and_solve(clauses: &mut std::vec::Vec<std::vec::Vec<i32>>, num_literals: usize) -> bool {
    let mut formula = Formula { clauses: Vec::new(), num_vars: num_literals };
    for clause in clauses {
        let mut currclause: Vec<Lit2> = vec![];
        for lit in clause {
            assert!(*lit != 0);
            if *lit < 0 {
                let new_lit = Lit2::new((lit.abs() - 1) as usize, false);
                currclause.push(new_lit);
            } else {
                let new_lit = Lit2::new((*lit - 1) as usize, true);
                currclause.push(new_lit);
            }
        }
        if currclause.len() == 0 {
            return false;
        } else {
            let clause2: Clause2 = Clause2::clause_from_vec(&currclause);
            formula.clauses.push(clause2);
        }
    }
    match solver(formula) {
        SatResult::Sat(_) => true,
        SatResult::Unsat => false,
        _ => panic!("Sarek should really make the parser non-binary"),
    }
}
