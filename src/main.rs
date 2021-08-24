use std::collections::HashSet;

type Literal = i32;
type Clause = Vec<Literal>;
type Clauses = Vec<Clause>;

fn consistent(clauses: &Clauses) -> bool {
    let mut seen = HashSet::new();
    for clause in clauses {
        for literal in clause {
            if seen.contains(&-*literal) {
                return false;
            }
            seen.insert(literal);
        }
    }
    return true;
}

fn contains_empty(clauses: &Clauses) -> bool {
    for clause in clauses {
        if clause.len() == 0 {
            return true;
        }
    }
    return false;
}

fn unit_propagate(clauses: &Clauses, literal: Literal) -> Clauses {
    let mut out_clauses = vec![];
    for clause in clauses {
        if !clause.contains(&literal) {
            let mut out_clause = vec![];
            for lit in clause {
                if lit != &-literal {
                    out_clause.push(*lit);
                }
            }
            out_clauses.push(out_clause);
        }
    }
    return out_clauses;
}

fn pure_literal_assign(clauses: &Clauses, literal: Literal) -> Clauses {
    let mut out_clauses = vec![];
    for clause in clauses {
        if !clause.contains(&literal) {
            let mut out_clause = vec![];
            for lit in clause {
                out_clause.push(*lit);
            }
            out_clauses.push(out_clause);
        }
    }
    return out_clauses;
}

fn choose_literal(_clauses: &Clauses, clause_counter: i32) -> Literal {
    return clause_counter;
}

fn dpll(clauses: &mut Clauses, clause_counter: i32) -> bool {
    if contains_empty(clauses) {
        return false;
    }
    if consistent(clauses) {
        return true;
    }
    let mut stabilized = false;
    while !stabilized {
        stabilized = true;
        for i in 0..clauses.len() {
            if clauses[i].len() == 1 {
                *clauses = unit_propagate(&clauses, clauses[i][0]);
                stabilized = false;
                break;
            }
        }
    }
    let mut pures = vec![];
    let mut seen = HashSet::new();
    for i in 0..clauses.len() {
        for &literal in &clauses[i] {
            seen.insert(literal);
        }
    }
    for literal in &seen {
        if !seen.contains(&-*literal) {
            pures.push(*literal);
        }
    }
    for literal in pures {
        *clauses = pure_literal_assign(&clauses, literal);
    }
    let literal = choose_literal(&clauses, clause_counter);
    let new_counter = clause_counter + 1;
    let mut clauses1 = clauses.clone();
    clauses1.push(vec![literal]);
    let mut clauses2 = clauses.clone();
    clauses2.push(vec![-literal]);
    return dpll(&mut clauses1, new_counter) || dpll(&mut clauses2, new_counter);
}

// TODO: Move to separate module
use std::fs::File;
use std::io::{self, BufRead};
use std::path::Path;

fn read_lines<P>(filename: P) -> io::Result<io::Lines<io::BufReader<File>>>
where
    P: AsRef<Path>,
{
    let file = File::open(filename)?;
    Ok(io::BufReader::new(file).lines())
}

fn parse_cnf(infile: &str) -> Clauses {
    /*
    let mut problem_type = "";
    let mut num_variables = 0;
    let mut num_clauses = 0;
    */
    let mut out_clauses = vec![];
    let mut curr_clause = vec![];
    if let Ok(lines) = read_lines(infile) {
        for line in lines {
            if let Ok(line) = line {
                let split = line.split(" ").collect::<Vec<_>>();
                if split.len() > 0 {
                    match split[0] {
                        "c" => {}
                        "p" => {}
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
    return out_clauses;
}

fn main() {
    /*
    let mut clauses = parse_cnf("cnfs/uf8.cnf");
    let mut clauses = parse_cnf("cnfs/empty-clause.cnf");
    let mut clauses = parse_cnf("cnfs/unsat.cnf");
    let mut clauses = parse_cnf("cnfs/uf20-01.cnf");
    let mut clauses = parse_cnf("cnfs/uf100-010.cnf");
    let mut clauses = parse_cnf("cnfs/unsat-ex01.cnf");
    */
    let mut clauses = parse_cnf("cnfs/uf250-02.cnf");
    println!("Parse complete");
    let result = dpll(&mut clauses, 1);
    if result {
        println!("Sat");
    } else {
        println!("Unsat");
    }
}
