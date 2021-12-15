use crate::assignments::*;
//use crate::clause::*;
use crate::formula::*;
use crate::lit::*;
use crate::trail::*;
use crate::watches::*;
use crate::trail::{Reason::*};

pub enum Conflict {
    Ground,
    Unit(Lit),
    Learned(usize, Lit, Vec<Lit>),
}

pub fn analyze_conflict(f: &Formula, a: &Assignments, trail: &Trail, decisionlevel: usize, cref: usize) -> Conflict {
    if decisionlevel == 0 {
        return Conflict::Ground;
    }
    assert!(decisionlevel > 0);
    // `seen` should be persistent across calls to `analyze_conflict`.
    // Solved by somehow keeping it in `solver`, either as a buffer or by making
    // conflict analysis a struct which is instatiated once and then kept.
    let mut seen = vec![false; f.num_vars]; 
    let mut out_learnt = vec![Lit{idx: 999999, polarity: false}; 1]; // I really don't like this way of reserving space.

    let mut path_c = 0;
    let mut confl = cref;
    //println!("Entry to analyze - curr trail: {:?}", trail.trail);
    let mut i = trail.trail.len() - 1;
    let mut j = trail.trail[i].len();
    loop {
        let base = if confl == cref {0} else {1};
        let mut k = base;
        let clause = &f.clauses[confl].0;
        //println!("Confl: {:?}, confl0 {:?}", confl, cref);
        //println!("Clause: {:?}", clause);
        while k < clause.len() {
            let lit = clause[k];
            //println!("Base: {:?} Lit: {:?}", base, lit);
            assert!(a.0[lit.idx] != None);
            if !seen[lit.idx] {
                let level = trail.vardata[lit.idx].0;
                //println!("Level: {:?}, Curr level: {:?}", level, decisionlevel);
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
        //println!("Trail: {:?}", trail.trail);
        let next = {
            loop { 
                j -= 1;
                if seen[trail.trail[i][j].idx] {
                    break;
                }
                else {
                    //println!("Seen");
                }

                if j == 0 {
                    i -= 1;
                    j = trail.trail[i].len();
                }
                //println!("{}, {}", i, j);
            }
            trail.trail[i][j]
        };
        //println!("Current out_learnt {:?}", out_learnt);
        seen[next.idx] = false;
        // now dlevel = i
        path_c -= 1;
        if path_c <= 0 {
            out_learnt[0] = !next;
            //println!("Final out_learnt {:?}", out_learnt);
            //println!("Done");
            break;
        }
        match &trail.vardata[(!next).idx].1 {
            Long(c) => {
                confl = *c; //println!("Reason: {}", confl);
            },
            Other => {
                panic!("Error - this has reason: {:?}", Other);
            }
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

