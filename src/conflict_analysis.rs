extern crate creusot_contracts;
use creusot_contracts::*;
use creusot_contracts::std::*;

use crate::assignments::*;
use crate::clause::*;
use crate::formula::*;
use crate::lit::*;
use crate::trail::*;
//use crate::watches::*;
use crate::trail::{Reason::*};

#[derive(Debug)]
pub enum Conflict {
    Ground,
    Unit(Lit),
    Learned(usize, Lit, Vec<Lit>),
}

fn resolve(_f: &Formula, c: &Clause, o: &Clause, idx: usize) -> Clause {
    let mut new = Vec::new();
    let mut i = 0;
    while i < c.rest.len() {
        if c.rest[i].idx != idx {
            new.push(c.rest[i]);
        }
        i += 1;
    }
    i = 0;
    while i < o.rest.len() {
        if o.rest[i].idx != idx {
            let mut k = 0;
            let mut broken = false;
            // Super bad way of removing duplis
            while k < new.len() {
                if new[k].idx == o.rest[i].idx {
                    broken = true;
                    break;
                }
                k += 1;
            }
            if !broken {
                new.push(o.rest[i]);
            }
        }
        i += 1;
    }
    Clause {
        rest: new,
    }
}

// Super bad / simple
fn choose_literal(c: &Clause, trail: &Trail, i: &mut usize, j: &mut usize) -> Lit {
    let next = {
        loop { 
            *j -= 1;
            let mut k = 0;
            let mut broken = false;
            while k < c.rest.len() {
                if trail.trail[*i][*j].idx == c.rest[k].idx {
                    broken = true;
                    break;
                }
                k += 1;
            }
            if broken {
                break;
            }
            if *j == 0 {
                *i -= 1;
                *j = trail.trail[*i].len();
            }
        }
        trail.trail[*i][*j]
    };
    next
}


// The "standard one" from Zha03
// Probs better to use as a base
// Might also be good to do the proof of the extension being OK inside this rather than do
// a return then add
#[trusted]
pub fn analyze_conflict_new(f: &Formula, a: &Assignments, trail: &Trail, cref: usize) -> Conflict {
    let decisionlevel = trail.trail.len() - 1;
    if decisionlevel == 0 {
        return Conflict::Ground;
    }
    // cl = find_conflicting_clause();
    /*
    loop {
        lit = choose_literal(cl);
        var = variable_of_literal(lit);
        ante = antecedent(var);
        cl = resolve(cl, ante, var);
        if stop_criterion_met(cl) {
            break;
        }
    }
    add_clause_to_database(cl);
    back_dl = clause_asserting_level(cl);
    return back_dl
    */
    // Making these persistent is strictly speaking an optimization
    let mut i = trail.trail.len() - 1;
    let mut j = trail.trail[i].len();
    let mut clause = f.clauses[cref].clone();
    loop {
    //i = trail.trail.len() - 1;
    //j = trail.trail[i].len();
        let lit = choose_literal(&clause, trail, &mut i, &mut j);
        let ante = match &trail.vardata[lit.idx].1 {
            Long(c) => f.clauses[*c].clone(),
            o => panic!(),
        };
        clause = resolve(f, &clause, &ante, lit.idx);
        let mut k = 0;
        let mut cnt = 0;
        while k < clause.rest.len() {
            if trail.vardata[clause.rest[k].idx].0 == decisionlevel {
                cnt += 1;
            }
            k += 1;
        }
        if cnt == 1 {
            break;
        }
    }
    if clause.rest.len() == 1 {
        Conflict::Unit(clause.rest[0])
    } else {
        Conflict::Learned(cref, clause.rest[0], clause.rest)
    }
}

#[trusted]
#[requires(f.invariant())]
#[requires(a.invariant(*f))]
#[requires(trail.invariant(*f))]
#[requires((@trail.trail).len() > 0)]
#[requires(@cref < (@f.clauses).len())]
#[ensures(match result {
    Conflict::Ground => f.unsat(*a),
    Conflict::Unit(lit) => {true}, // know lit can be learned
    Conflict::Learned(level, lit, clause) => {
        @level > 0 && @level <= (@trail.trail).len() &&
        @lit.idx < ((@a).len()) && // can be changed to lit in or somet
        (@clause).len() > 1 &&
        vars_in_range_inner(@clause, @f.num_vars) &&
        no_duplicate_indexes_inner(@clause) &&
        true
    }, // know clause can be learned
})]
pub fn analyze_conflict(f: &Formula, a: &Assignments, trail: &Trail, cref: usize) -> Conflict {
    let decisionlevel = trail.trail.len() - 1;
    if decisionlevel == 0 {
        return Conflict::Ground;
    }
    // `seen` should be persistent across calls to `analyze_conflict`.
    // Solved by somehow keeping it in `solver`, either as a buffer or by making
    // conflict analysis a struct which is instatiated once and then kept.
    let mut seen = vec::from_elem(false, f.num_vars); //vec![false; f.num_vars]; 
    //let mut out_learnt = vec![Lit{idx: 999999, polarity: false}; 1]; // I really don't like this way of reserving space.
    let mut out_learnt = Vec::new();
    out_learnt.push(Lit{idx: 999999, polarity: false});

    let mut path_c = 0;
    let mut confl = cref;
    let mut i = trail.trail.len() - 1;
    let mut j = trail.trail[i].len();
    loop {
        let base = if confl == cref {0} else {1};
        let mut k = base;
        let clause = &f.clauses[confl].rest;
        while k < clause.len() {
            let lit = clause[k];
            if !seen[lit.idx] {
                let level = trail.vardata[lit.idx].0;
                if level > 0 {
                    seen[lit.idx] = true;
                    if level >= decisionlevel {
                        path_c += 1;
                    } else {
                        out_learnt.push(lit);
                    }
                }
            }
            k += 1;
        }
        let next = {
            loop { 
                j -= 1;
                if seen[trail.trail[i][j].idx] {
                    break;
                }
                if j == 0 {
                    i -= 1;
                    j = trail.trail[i].len();
                }
            }
            trail.trail[i][j]
        };
        seen[next.idx] = false;
        // now dlevel = i
        path_c -= 1;
        if path_c <= 0 {
            out_learnt[0] = !next;
            break;
        }
        match &trail.vardata[(!next).idx].1 {
            Long(c) => confl = *c,
            //other => panic!("Error - this has reason: {:?}", other),
            _other => panic!(),
        }
    }
    if out_learnt.len() == 1 {
        return Conflict::Unit(out_learnt[0]);
    } else {
        let mut max_i = 1;
        let mut max_level = trail.vardata[out_learnt[1].idx].0;
        for i in 2..out_learnt.len() {
            let level = trail.vardata[out_learnt[i].idx].0;
            if level > max_level {
                max_level = level;
                max_i = i;
            }
        }
        out_learnt.swap(1, max_i);
        return Conflict::Learned(max_level, out_learnt[0], out_learnt);
    }
}