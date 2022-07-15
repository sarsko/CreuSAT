use core::panic;

use crate::{
    clause::*,
    decision::*,
    formula::*,
    lit::*,
    minimize::*,
    solver::{SearchMode, Solver},
    trail::*,
};

#[derive(Debug)]
pub enum Conflict {
    Ground,
    Unit(Lit),
    Learned(u32, Clause),
}

pub(crate) fn analyze_conflict(
    formula: &Formula, trail: &Trail, cref: usize, decisions: &mut impl Decisions, solver: &mut Solver,
) -> Conflict {
    let decisionlevel = trail.decision_level();
    if decisionlevel == 0 {
        return Conflict::Ground;
    }
    // I tried moving seen to solver, but it wasn't really any faster (+ it is nice to not have to carry the invariant that seen is all false)
    let mut to_bump = Vec::new(); // VMTF and VSIDS
    let mut seen = vec![false; formula.num_vars];
    let mut out_learnt: Vec<Lit> = vec![Lit::new(0, true); 1]; // I really don't like this way of reserving space.
    let mut path_c = 0;
    let mut confl = cref;
    let mut i = trail.trail.len();
    loop {
        let clause = &formula[confl];
        let mut k = if confl == cref { 0 } else { 1 };
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
                    decisions.bump_variable(lit.index());
                    if solver.search_mode == SearchMode::Stable || solver.search_mode == SearchMode::OnlyStable {
                        decisions.bump_reason_literals(lit.index(), trail, formula);
                    }
                    seen[lit.index()] = true;

                    //to_bump.push(lit.index()); // VMTF

                    if level >= decisionlevel {
                        path_c += 1;

                        // VSIDS:
                        let reason_ref = trail.lit_to_reason[lit.index()];
                        if reason_ref != UNSET_REASON && reason_ref >= solver.initial_len {
                            to_bump.push(lit.index());
                        }
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
        confl = next.reason;
    }
    // decisions.bump_vec_of_vars(f, to_bump); // VMTF. NO-OP for VSIDS

    recursive_minimization(&mut out_learnt, trail, formula, solver, seen);

    if out_learnt.len() == 1 {
        Conflict::Unit(out_learnt[0])
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
        let mut clause = Clause::new(out_learnt);
        clause.calc_and_set_lbd(trail, solver);
        let lbd = clause.lbd;

        // VSIDS:
        // UPDATEVARACTIVITY trick (see competition'09 companion paper)
        if solver.search_mode == SearchMode::Focus || solver.search_mode == SearchMode::OnlyFocus {
            for var in to_bump.iter() {
                if formula[trail.lit_to_reason[*var]].lbd < lbd {
                    decisions.bump_variable(*var);
                }
            }
        }

        Conflict::Learned(max_level, clause)
    }
}
