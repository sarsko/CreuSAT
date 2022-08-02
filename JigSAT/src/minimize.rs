use crate::{
    formula::Formula,
    lit::Lit,
    solver::Solver,
    trail::{Trail, UNSET_REASON},
};

#[inline(always)]
pub(crate) fn lit_redundant(
    solver: &mut Solver, trail: &Trail, formula: &Formula, lit: Lit, abstract_levels: u32, seen: &mut [bool],
) -> bool {
    solver.analyze_stack.clear();
    solver.analyze_stack.push(lit);
    let top = solver.analyze_toclear.len();
    while !solver.analyze_stack.is_empty() {
        //assert(reason(var(analyze_stack.last())) != CRef_Undef);
        let ante_ref = trail.lit_to_reason[solver.analyze_stack.pop().unwrap().index()];
        let c = &formula.clauses[ante_ref];
        /*
        // This should not be possible. I guess Glucose has a relaxed invariant for binary clauses.
        if c.len() == 2 && c[0].lit_unsat(assignments) {
            assert(value(c[1]) == l_True);
            Lit tmp = c[0];
            c[0] = c[1], c[1] = tmp;
        }
        */
        let mut i = 1;

        while i < c.len() {
            let p2 = c[i];
            if !seen[p2.index()] && trail.lit_to_level[p2.index()] > 0 {
                if trail.lit_to_reason[p2.index()] != UNSET_REASON
                    && p2.abstract_level(&trail.lit_to_level) & abstract_levels != 0
                {
                    seen[p2.index()] = true;
                    solver.analyze_stack.push(p2);
                    solver.analyze_toclear.push(p2);
                } else {
                    let mut j = top;
                    while j < solver.analyze_toclear.len() {
                        seen[solver.analyze_toclear[j].index()] = false;
                        j += 1;
                    }
                    solver.analyze_toclear.truncate(top);
                    return false;
                }
            }
            i += 1;
        }
    }
    true
}

#[allow(unused)]
#[inline(always)]
pub(crate) fn recursive_minimization(
    out_learnt: &mut Vec<Lit>, trail: &Trail, formula: &Formula, solver: &mut Solver, mut seen: Vec<bool>,
) {
    let mut abstract_levels = 0;
    let mut i = 1;
    while i < out_learnt.len() {
        abstract_levels |= out_learnt[i].abstract_level(&trail.lit_to_level);
        i += 1;
    }
    i = 1;
    let mut j = 1;
    while i < out_learnt.len() {
        let ante_ref = trail.lit_to_reason[out_learnt[i].index()];
        if ante_ref == UNSET_REASON || !lit_redundant(solver, trail, formula, out_learnt[i], abstract_levels, &mut seen)
        {
            out_learnt[j] = out_learnt[i];
            j += 1;
        }
        i += 1;
    }
    out_learnt.truncate(j);
}

#[allow(unused)]
#[inline(always)]
pub(crate) fn local_minimization(out_learnt: &mut Vec<Lit>, trail: &Trail, formula: &Formula, seen: Vec<bool>) {
    let mut i = 1;
    let mut j = 1;
    while i < out_learnt.len() {
        let ante_ref = trail.lit_to_reason[out_learnt[i].index()];
        if ante_ref == UNSET_REASON {
            out_learnt[j] = out_learnt[i];
            j += 1;
        } else {
            let ante = &formula.clauses[ante_ref];
            let mut k = if ante.len() == 2 { 0 } else { 1 };
            while k < ante.len() {
                let idx = ante[k].index();
                if !seen[idx] && trail.lit_to_level[idx] > 0 {
                    out_learnt[j] = out_learnt[i];
                    j += 1;
                    break;
                }
                k += 1;
            }
        }
        i += 1;
    }
    out_learnt.truncate(j);
}
