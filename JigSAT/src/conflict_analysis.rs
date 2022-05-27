use crate::{clause::*, formula::*, lit::*, trail::*, unit_prop::Conflict};
use std::slice::from_ref;

//#[derive(Debug)]
pub enum ConflictRes {
    Ground,
    Unit(Lit),
    Binary(Lit, Lit),
    Learned(u32, Clause),
}

pub fn analyze_conflict(f: &Formula, trail: &Trail, confl: Conflict) -> ConflictRes {
    let decisionlevel = trail.decision_level();
    if decisionlevel == 0 {
        return ConflictRes::Ground;
    }
    // `seen` should be persistent across calls to `analyze_conflict`.
    // Solved by somehow keeping it in `solver`, either as a buffer or by making
    // conflict analysis a struct which is instatiated once and then kept.
    let mut seen = vec![false; f.num_vars];
    let mut out_learnt:Vec<Lit> = vec![Lit::new(0, true); 1]; // I really don't like this way of reserving space.
    let mut path_c = 0;
    let mut perm_lits = Vec::new();
    let mut clause: &[Lit] = match confl {
        Conflict::Binary(lits) => {
            for lit in lits {
                perm_lits.push(lit);
            }
            &perm_lits[..]
        },
        Conflict::Long(cref) => &f[cref].rest[..],
    };
    let mut i = trail.trail.len();
    loop {
        let mut k = 0;
        while k < clause.len() {
            let lit = clause[k];
            if !seen[lit.index()] {
                let level = trail.lit_to_level[lit.index()];
                /* 
                // This is nonsensical as we are not wiping lit_to_level anymore.
                if level == u32::MAX {
                    panic!();
                }
                */
                if level > 0 {
                    seen[lit.index()] = true;
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
                i -= 1;
                if seen[trail.trail[i].lit.index()] {
                    break;
                }
            }
            &trail.trail[i]
        };
        seen[next.lit.index()] = false;
        path_c -= 1;
        if path_c == 0 {
            out_learnt[0] = !next.lit;
            break;
        }
        clause = match &next.reason {
            Reason::Long(c) => &f[*c].rest[1..],
            Reason::Binary(lit) => {
                //let p_len = perm_lits.len();
                //perm_lits.push(*lit);
                //&perm_lits[p_len..]
                from_ref(lit)
            }
            other => panic!("{:?}", other),
        }
    }
    if out_learnt.len() == 1 {
        return ConflictRes::Unit(out_learnt[0]);
    } else if out_learnt.len() == 2 {
        return ConflictRes::Binary(out_learnt[0], out_learnt[1]);
    } else {
        let mut max_i: usize = 1;
        let mut max_level = trail.lit_to_level[out_learnt[1].index()];
        i = 2;
        while i < out_learnt.len() {
            let level = trail.lit_to_level[out_learnt[i].index()];
            if level > max_level {
                max_level = level;
                max_i = i;
            }
            i += 1;
        }
        out_learnt.swap(1, max_i);
        ConflictRes::Learned(max_level, Clause{ deleted: false, lbd: 0, search: 2, rest: out_learnt})
    }
}