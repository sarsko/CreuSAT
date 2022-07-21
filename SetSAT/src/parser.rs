use std::fs::File;
use std::io::{self, BufRead};
use std::path::Path;

use crate::solver::*;

#[cfg(not(feature = "contracts"))]
fn read_lines<P>(filename: P) -> io::Result<io::Lines<io::BufReader<File>>>
where
    P: AsRef<Path>,
{
    let file = File::open(filename)?;
    Ok(io::BufReader::new(file).lines())
}
#[cfg(not(feature = "contracts"))]
pub fn parse_cnf(infile: &str) -> Result<ClauseDB, String> {
    /*
    let mut problem_type = "";
    let mut num_clauses = 0;
    */
    use std::collections::HashSet;
    let mut num_literals = 0;
    let mut num_lits_set = false;

    let mut clause_db = ClauseDB::new();
    let mut curr_clause = vec![];

    let mut line_cntr = 0;
    let mut max_literal: usize = 0;
    let mut seen = HashSet::new();
    let mut tautology = false;
    if let Ok(lines) = read_lines(infile) {
        for line in lines {
            line_cntr += 1;
            if let Ok(line) = line {
                let split = line.split(' ').filter(|e| e != &"").collect::<Vec<_>>();
                if split.len() > 0 {
                    match split[0].chars().next().unwrap() {
                        'c' => {}
                        'p' => { /*match split[2].parse::<usize>() {
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
                             */
                        }
                        '%' => {
                            break;
                        } // The Satlib files follow this convention
                        _ => {
                            for e in split {
                                match e.parse::<i32>() {
                                    Ok(n) => {
                                        if n == 0 {
                                            if !tautology {
                                                clause_db.add_unwatched_clause(Clause::new(curr_clause));
                                            }
                                            tautology = false;
                                            seen = HashSet::new();
                                            curr_clause = vec![];
                                        } else if seen.contains(&-n) {
                                            tautology = true;
                                        } else {
                                            let n_abs = n.unsigned_abs() as usize;
                                            if n_abs > max_literal {
                                                max_literal = n_abs;
                                            }
                                            if !seen.contains(&n) {
                                                curr_clause.push(Lit::from_dimacs(n));
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
    Ok(clause_db)
}
