use std::fs::File;
use std::io::{self, BufRead};
use std::path::Path;

use crate::types::*;

fn read_lines<P>(filename: P) -> io::Result<io::Lines<io::BufReader<File>>>
where
    P: AsRef<Path>,
{
    let file = File::open(filename)?;
    Ok(io::BufReader::new(file).lines())
}

pub fn parse_cnf(infile: &str) -> (Clauses, usize) {
    /*
    let mut problem_type = "";
    let mut num_clauses = 0;
    */
    let mut num_literals = 0;
    let mut out_clauses = vec![];
    let mut curr_clause = vec![];
    if let Ok(lines) = read_lines(infile) {
        for line in lines {
            if let Ok(line) = line {
                let split = line.split(" ").filter(|e| e != &"").collect::<Vec<_>>();
                if split.len() > 0 {
                    match split[0] {
                        "c" => {}
                        "p" => {
                            match split[2].parse::<i32>() {
                                Ok(n) => { num_literals = n },
                                Err(_) => { panic!("Error in input file"); }
                            }
                        }
                        _ => {
                            for e in split {
                                match e.parse::<i32>() {
                                    Ok(n) => {
                                        if n == 0 {
                                            out_clauses.push(curr_clause);
                                            curr_clause = vec![];
                                        } else {
                                            curr_clause.push(n);
                                        }
                                    }
                                    Err(_) => panic!("Error in input file"),
                                }
                            }
                        }
                    }
                }
            }
        }
    }
    else {
        panic!("File not found!");
    }
    return (out_clauses, num_literals as usize);
}
