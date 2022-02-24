extern crate creusot_contracts;

use creusot_contracts::*;
use creusot_contracts::std::*;

use crate::assignments::*;
use crate::clause::*;
use crate::formula::*;
use crate::lit::*;
use crate::trail::*;
use crate::watches::*;
use crate::conflict_analysis::*;

// FIX
#[trusted] // Checks out(but the trail invariant takes some time)
/*
#[requires(@cref < (@f.clauses).len())]
//#[requires(@i < @j)]
#[requires(@j < (@(@f.clauses)[@cref]).len() && @i < (@(@f.clauses)[@cref]).len())]
#[requires(f.invariant())]
#[requires(_t.invariant(*f))]
*/
#[ensures((^f).invariant())]
#[ensures(_t.invariant(^f))]
#[ensures(@f.num_vars === @(^f).num_vars)]
#[ensures((@(^f).clauses).len() === (@f.clauses).len())]
#[ensures(forall<i: Int> 0 <= i && i < (@(^f).clauses).len() ==>
    (@(@(^f).clauses)[i]).len() === (@(@f.clauses)[i]).len())] // Needed for watches, can be rewritten
#[ensures((@(@(^f).clauses)[@cref]).exchange(@(@f.clauses)[@cref], @i, @j))]
fn swap_lits(f: &mut Formula, cref: usize, i: usize, j: usize, _t: &Trail) {
    f.clauses[cref].rest.swap(i, j);
}

#[trusted]
/*
#[requires(f.invariant())]
#[requires(a.invariant(@f.num_vars))]
#[requires(trail.invariant(*f))]
#[requires(watches.invariant(*f))]
#[requires(@f.num_vars < @usize::MAX/2)]
#[requires((@trail.trail).len() > 0)]
*/
#[ensures((^f).invariant())]
#[ensures((^a).invariant(@f.num_vars))]
#[ensures((^trail).invariant(^f))]
#[ensures((^watches).invariant(^f))]
#[ensures(@f.num_vars === @(^f).num_vars)]
#[ensures((@(^f).clauses).len() === (@f.clauses).len())]
#[ensures((@(^trail).trail).len() === (@trail.trail).len())]
#[ensures(match result {
    Ok(()) => true,
    Err(cref) => @cref < (@(^f).clauses).len() 
})]
fn mock_unit_propagate(f: &mut Formula, a: &mut Assignments, trail: &mut Trail, watches: &mut Watches) -> Result<(), usize> {
    Ok(())
}

#[trusted]
/*
#[requires(f.invariant())]
#[requires(a.invariant(@f.num_vars))]
#[requires(trail.invariant(*f))]
#[requires(_w.invariant(*f))]
#[requires(@f.num_vars < @usize::MAX/2)]
#[requires((@trail.trail).len() > 0)]
#[requires(@cref < (@f.clauses).len())]
*/
#[ensures(match result {
    Conflict::Ground => true,
    Conflict::Unit(lit) => 0 <= @lit.idx && @lit.idx < @f.num_vars,
    Conflict::Learned(level, lit, reason) => 0 <= @lit.idx && @lit.idx < @f.num_vars
    //&& @level > 0  // Is this actually true? I don't think so.
    && @level < (@trail.trail).len() && (@reason).len() > 1 &&
    (forall<i: Int> 0 <= i && i < (@reason).len() ==>
        (@(@reason)[i].idx < @f.num_vars &&
        (((@reason)[i])).to_neg_watchidx_logic() < (@_w.watches).len() 
        ))
    , // Watch out
})]
pub fn mock_analyze_conflict(f: &Formula, a: &Assignments, trail: &Trail, cref: usize, _w: &Watches) -> Conflict {
    return Conflict::Ground;
}

#[trusted]// OK
/*
#[requires((@trail.trail).len() > 0)]
#[requires(0 <= @lit.idx && @lit.idx < (@trail.vardata).len())]
#[requires(0 <= @lit.idx && @lit.idx < (@a).len())]
#[requires(trail.invariant(*_f))]
#[requires(a.invariant(@_f.num_vars))]
*/
#[ensures((^a).invariant(@_f.num_vars))]
#[ensures((^trail).invariant(*_f))]
#[ensures((@(^trail).trail).len() === 1)]
pub fn mock_learn_unit(a: &mut Assignments, trail: &mut Trail, lit: Lit, _f: &Formula) {
    a.mock_cancel_until(trail, 1, _f);
    // Postcond for cancel_until has to be updated so that the entry is guaranteed to be none.
    //proof_assert! {(@a)[@lit.idx] === None }
    a.set_assignment(lit, _f);
    trail.enq_assignment(lit, Reason::Unit, _f);
}

#[requires((@f.clauses).len() > 0)]
#[requires(f.invariant())]
#[requires(a.invariant(@f.num_vars))]
#[requires(trail.invariant(*f))]
#[requires(watches.invariant(*f))]
#[requires(@f.num_vars < @usize::MAX/2)]
#[requires((@trail.trail).len() === 1)]
//#[ensures(result ==> f.eventually_sat(*a))]
//#[ensures(result === false ==> !f.eventually_sat_complete(*a))]
fn solve(f: &mut Formula, a: &mut Assignments, trail: &mut Trail, watches: &mut Watches) -> bool {
    loop {
        loop {
            match mock_unit_propagate(f, a, trail, watches) {
                Ok(_) => { break; },
                Err(cref) => {
                    match mock_analyze_conflict(f, a, trail, cref, watches) {
                        Conflict::Ground => { return false; },
                        Conflict::Unit(lit) => {
                            mock_learn_unit(a, trail, lit, f);
                        }
                        Conflict::Learned(level, lit, clause) => {
                            a.mock_cancel_until(trail, level, f);
                            trail.mock_add_level(f);
                            a.mock_set_assignment(lit, f);
                            let cref = f.mock_add_clause(&clause, watches);
                            trail.mock_enq_assignment(lit, Reason::Long(cref), f);
                        }
                    }
                },
            }
        }
        if let Some(lit) = a.find_unassigned_lit() {
            let lit = lit; // Due to issue #273
            //trail.trail.push(Vec::new());
            trail.mock_add_level(f);
            a.mock_set_assignment(lit, f);
            trail.mock_enq_assignment(lit, Reason::Decision, f);
        } else {
            return true;
        } 
    }
}