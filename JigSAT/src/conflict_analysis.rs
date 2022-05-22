use crate::{assignments::*, clause::*, formula::*, lit::*, trail::*};

//#[derive(Debug)]
pub enum Conflict {
    Ground,
    Unit(Lit),
    Learned(u32, Clause),
    Panic,
}

pub fn analyze_conflict(f: &Formula, trail: &Trail, cref: usize) -> Conflict {
    let decisionlevel = trail.decision_level();
    if decisionlevel == 0 {
        return Conflict::Ground;
    }
    // `seen` should be persistent across calls to `analyze_conflict`.
    // Solved by somehow keeping it in `solver`, either as a buffer or by making
    // conflict analysis a struct which is instatiated once and then kept.
    let mut seen = vec![false; f.num_vars];
    let mut out_learnt:Vec<Lit> = vec![Lit::new(0, true); 1]; // I really don't like this way of reserving space.
    let mut path_c = 0;
    let mut confl = cref;
    let mut i = trail.trail.len();
    loop {
        let clause = &f.clauses[confl];
        let mut k = if confl == cref {0} else {1};
        while k < clause.len() {
            let lit = clause[k];
            if !seen[lit.index()] {
                let level = trail.lit_to_level[lit.index()];
                if level == u32::MAX {
                    panic!();
                }
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
        // now dlevel = i
        path_c -= 1;
        if path_c <= 0 {
            out_learnt[0] = !next.lit;
            break;
        }
        match &next.reason {
            Reason::Long(c) => confl = *c,
            other => panic!("{:?}", other),
        }
    }
    if out_learnt.len() == 1 {
        return Conflict::Unit(out_learnt[0]);
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
        Conflict::Learned(max_level, Clause{ deleted: false, lbd: 0, rest: out_learnt})
    }
}