use crate::{
    formula::Formula,
    lit::Lit,
    solver::Solver,
    trail::{Trail, UNSET_REASON},
};

pub fn lit_redundant(
    solver: &mut Solver, trail: &Trail, formula: &Formula, lit: Lit, abstract_levels: u32, seen: &mut Vec<bool>,
) -> bool {
    solver.analyze_stack.clear();
    solver.analyze_stack.push(lit);
    let top = solver.analyze_toclear.len();
    while solver.analyze_stack.len() > 0 {
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
    return true;
}
