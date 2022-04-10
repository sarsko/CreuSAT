extern crate creusot_contracts;
use creusot_contracts::*;
use creusot_contracts::std::*;

use crate::{
    assignments::*,
    clause::*,
    formula::*,
    lit::*,
    trail::*,
};

#[cfg(contracts)]
use crate::logic::{
    logic_clause::*,
    logic_conflict_analysis::*,
    logic_formula::*,
    logic::*,
};

//#[derive(Debug)]
pub enum Conflict {
    Ground,
    Unit(Lit),
    //Learned(usize, Lit, Vec<Lit>),
    Learned(usize, Lit, Clause),
    Panic,
}

// Both of these should be changed to unary_ok, but things are checking out somehow

#[cfg_attr(all(any(trust_conflict, trust_all), not(untrust_all)), trusted)]
#[ensures(result === (exists<i: Int> 0 <= i && i < (@v).len() && @(@v)[i].idx === @idx))]
fn idx_in(v: &Vec<Lit>, idx: usize) -> bool {
    let mut i: usize = 0;
    #[invariant(i_less, 0 <= @i && @i <= (@v).len())]
    #[invariant(not_idx, forall<j: Int> 0 <= j && j < @i ==> @(@v)[j].idx != @idx)]
    while i < v.len() {
        let lit = &v[i];
        if lit.idx == idx {
            return true;
        }
        i += 1;
    }
    false
}

//#[trusted] // OK [04.04] [[Doesnt check out on Mac [04.04] - struggling with the loop invariants, but that's it]]
//#[trusted] // Come back to it later. Invariant is sticky
#[cfg_attr(all(any(trust_conflict, trust_all), not(untrust_all)), trusted)]
#[requires(_f.invariant())]
#[requires(equisat_extension_inner(*c, @_f))]
#[requires(o.in_formula(*_f))]
#[requires(@c_idx < (@c).len() && @(@c)[@c_idx].idx === @idx &&
    (exists<k: Int> 0 <= k && k < (@o).len() &&
        (@o)[k].is_opp((@c)[@c_idx]))
)]
#[requires(forall<j: Int, k: Int> 0 <= j && j < (@o).len() && 0 <= k && k < (@c).len() &&
    k != @c_idx && @(@o)[j].idx != @idx ==> !(@c)[k].is_opp((@o)[j]))]
#[requires(c.same_idx_same_polarity_except(*o, @idx))]
#[requires(@idx < @_f.num_vars)]
#[ensures(equisat_extension_inner(result, @_f))]
#[ensures(result.invariant_unary_ok(@_f.num_vars))]
#[ensures(result.vars_in_range(@_f.num_vars))]
#[requires(o.post_unit_inner(@_a))]
#[requires(c.invariant_unary_ok(@_f.num_vars))]
#[requires(o.invariant_unary_ok(@_f.num_vars))]
#[requires(c.unsat_inner(@_a))]
#[ensures(result.unsat_inner(@_a))]
#[ensures((@result).len() > 0)] // TODO: Need to prove this
fn resolve(_f: &Formula, c: &Clause, o: &Clause, idx: usize, c_idx: usize, _a: &Assignments) -> Clause {
    let mut new: Vec<Lit> = Vec::new();
    let mut i: usize = 0;
    #[invariant(i_less, @i <= (@c.rest).len())]
    #[invariant(new_elems, forall<j: Int> 0 <= j && j < (@new).len() ==> 
        (@new)[j].invariant(@_f.num_vars))]
    #[invariant(no_dups, forall<j: Int, k: Int> 0 <= j && j < (@new).len() && 0 <= k && k < j ==>
        @(@new)[j].idx != @(@new)[k].idx)]
    #[invariant(not_idx, forall<j: Int> 0 <= j && j < (@new).len() ==> @(@new)[j].idx != @idx)]
    #[invariant(resolve, forall<j: Int> 0 <= j && j < @i && @(@c)[j].idx != @idx ==> 
        (@c)[j].lit_in_internal(@new))]
    #[invariant(from_c, forall<j: Int> 0 <= j && j < (@new).len() ==> (@new)[j].lit_in(*c))]
    #[invariant(res2, (forall<j: Int> 0 <= j && j < @i && j != @c_idx ==> 
        (@c)[j].lit_in_internal(@new)))]
    while i < c.rest.len() {
        let old_new = Ghost::record(&new);
        if idx_in(&new, c.rest[i].idx) {
            proof_assert!(@new === @@old_new);
        } else if c.rest[i].idx == idx {
            proof_assert!(@new === @@old_new);
        } else {
            new.push(c.rest[i]);
            proof_assert!((@new)[(@new).len() - 1] === (@c.rest)[@i]);
            proof_assert!((@new)[(@new).len() - 1].lit_in(*c));
        }
        i += 1;
    }
    let mut _o_idx: Option<usize> = None;
    let old_new = Ghost::record(&new);
    proof_assert!(@new === @@old_new);
    proof_assert!(forall<j: Int> 0 <= j && j < (@@old_new).len() ==> 
        (@new)[j] === (@@old_new)[j]);
    i = 0;
    #[invariant(i_less, @i <= (@o.rest).len())]
    #[invariant(new_elems, forall<j: Int> 0 <= j && j < (@new).len() ==> 
        (@new)[j].invariant(@_f.num_vars))]
    #[invariant(no_dups, forall<j: Int, k: Int> 0 <= j && j < (@new).len() && 0 <= k && k < j ==>
        @(@new)[j].idx != @(@new)[k].idx)]
    #[invariant(not_idx, forall<j: Int> 0 <= j && j < (@new).len() ==> @(@new)[j].idx != @idx)]
    #[invariant(resolve, forall<j: Int> 0 <= j && j < @i && @(@o)[j].idx != @idx ==> 
        (@o)[j].lit_in_internal(@new))]
    #[invariant(from_o, forall<j: Int> 0 <= j && j < (@new).len() - (@@old_new).len() ==> (@new)[(@@old_new).len() + j].lit_in(*o))]
    #[invariant(from_c, forall<j: Int> 0 <= j && j < (@@old_new).len() ==> (@new)[j].lit_in(*c))]
    #[invariant(old_unchanged, forall<j: Int> 0 <= j && j < (@@old_new).len() ==> 
        (@new)[j] === (@@old_new)[j])]
    #[invariant(maintains, 
            (forall<j: Int> 0 <= j && j < (@c ).len() && @(@c )[j].idx != @idx ==> (@c )[j].lit_in_internal(@new))
    )]
    #[invariant(new_sourced, forall<j: Int> 0 <= j && j < (@new).len() ==> 
                (@new)[j].lit_in_internal(@c) || (@new)[j].lit_in_internal(@o))]
    #[invariant(confl_idx, match _o_idx {
        None => forall<j: Int> 0 <= j && j < @i ==> @(@o)[j].idx != @idx,
        Some(j) => @(@o)[@j].idx === @idx
    })]
    #[invariant(res2, match _o_idx {
        None => (forall<j: Int> 0 <= j && j < @i ==> 
        (@o)[j].lit_in_internal(@new)),
        Some(k) => {@k < @i && (forall<j: Int> 0 <= j && j < @i && j != @k ==> 
        (@o)[j].lit_in_internal(@new))}
    })]
    #[invariant(res, (forall<j: Int> 0 <= j && j < (@c).len() && j != @c_idx ==> 
        (@c)[j].lit_in_internal(@new)))]
    while i < o.rest.len() {
        /*
        if !idx_in(&new, o.rest[i].idx) && o.rest[i].idx != idx {
            new.push(o.rest[i]);
        }
        */
        let old_new2 = Ghost::record(&new);
        proof_assert!(forall<j: Int> 0 <= j && j < (@@old_new).len() ==> 
            (@@old_new2)[j] === (@@old_new)[j]);
        proof_assert!(forall<j: Int> 0 <= j && j < (@@old_new).len() ==> 
            (@new)[j] === (@@old_new)[j]);
        proof_assert!(@new === @@old_new2);
        if idx_in(&new, o.rest[i].idx) {
            proof_assert!(@new === @@old_new2);
            proof_assert!(@c_idx < (@c).len() && @(@c)[@c_idx].idx === @idx &&
                (exists<k: Int> 0 <= k && k < (@o).len() && k != @i &&
                    (@o)[k].is_opp((@c)[@c_idx]))
            );
            proof_assert!(forall<j: Int, k: Int> 0 <= j && j < (@o).len() && 0 <= k && k < (@c).len() &&
                k != @c_idx && @(@o)[j].idx != @idx ==> !(@c)[k].is_opp((@o)[j]));
            proof_assert!(o.invariant_unary_ok(@_f.num_vars));
            proof_assert!(c.invariant_unary_ok(@_f.num_vars));
            //proof_assert!(forall<j: Int> 0 <= j && j < (@c ).len() && @(@c )[j].idx != @idx ==> (@c )[j].lit_in_internal(@new));
            //proof_assert!(exists<k: Int> 0 <= k && k < (@c).len() && @(@o)[@i].idx === @(@c)[k].idx);
            proof_assert!(0 <= @i && @i < (@o).len() && @(@o)[@i].idx != @idx);
            //proof_assert!(invariant_internal(@o, @_f.num_vars));
            //proof_assert!(invariant_internal(@c, @_f.num_vars));
            proof_assert!(forall<j: Int> 0 <= j && j < (@c).len() && @(@c)[j].idx != @idx ==> (@c)[j].lit_in_internal(@new));
            proof_assert!(lemma_idx(@c, @o, @new, @i, @idx, @c_idx, *_f); true);
            proof_assert!(forall<j: Int> 0 <= j && j < (@new).len() ==> (@new)[j].lit_in_internal(@c) || (@new)[j].lit_in_internal(@o));
            proof_assert!(exists<k: Int> 0 <= k && k < (@new).len() && @(@o)[@i].idx === @(@new)[k].idx);

            proof_assert!(lemma_idx2(@c, @o, @new, @i, @idx, @c_idx, *_f); 
                (@o)[@i].lit_in_internal(@new)
        );

        } else if o.rest[i].idx == idx {
            proof_assert!(@new === @@old_new2);
            proof_assert!(@(@o)[@i].idx === @idx);
            _o_idx = Some(i);
        } else {
            new.push(o.rest[i]);
            proof_assert!((@new)[(@new).len() - 1] === (@o.rest)[@i]);
            proof_assert!((@new)[(@new).len() - 1].lit_in(*o));
            proof_assert!(forall<j: Int> 0 <= j && j < (@@old_new2).len() ==> 
                (@new)[j] === (@@old_new2)[j]);
            proof_assert!(forall<j: Int> 0 <= j && j < (@@old_new).len() ==> 
                (@new)[j] === (@@old_new)[j]);
            proof_assert!(forall<j: Int> 0 <= j && j < (@@old_new).len() ==> 
                (@@old_new2)[j] === (@@old_new)[j]);
            proof_assert!((@o)[@i].lit_in_internal(@new));
        }
        proof_assert!(forall<j: Int> 0 <= j && j < (@@old_new).len() ==> 
            (@@old_new2)[j] === (@@old_new)[j]);
        proof_assert!(forall<j: Int> 0 <= j && j < (@@old_new).len() ==> 
            (@new)[j] === (@@old_new)[j]);
        i += 1;
    }
    let out = Clause {
        rest: new,
    };
    proof_assert!(@out === @new);
    proof_assert!(
            (forall<i: Int> 0 <= i && i < (@o).len() && @(@o)[i].idx != @idx ==> (@o)[i].lit_in_internal(@new))
    );
    proof_assert!(
    (exists<k: Int, m: Int> 0 <= k && k < (@o).len() && 0 <= m && m < (@c).len() &&
        @(@c)[m].idx === @idx && @(@o)[k].idx === @idx && (@o)[k].is_opp((@c)[m]))
    );

    proof_assert!(out.resolvent_of_idx(*c, *o, @idx));
    //proof_assert!(out.invariant(@_f.num_vars));

    match _o_idx {
        Some(o_idx) => {
            proof_assert!(forall<j: Int> 0 <= j && j < (@c).len() && j != @c_idx ==> 
            (@c)[j].lit_in(out));
            proof_assert!(forall<j: Int> 0 <= j && j < (@o).len() && j != @o_idx ==> 
            (@o)[j].lit_in(out));
            proof_assert!(formula_invariant(@_f));
            proof_assert!(equisat_extension_inner(*c, @_f));
            proof_assert!(o.in_formula_inner(@_f));
            proof_assert!(out.resolvent_of(*c, *o, @o_idx, @c_idx));
            proof_assert!(lemma_resolvent_of_equisat_extension_is_equisat(@_f, *c, *o, out, @c_idx, @o_idx);true);
            proof_assert!(equisat_extension_inner(out, @_f));
            //proof_assert!(lemma_resolved_post_and_unsat_is_unsat(*o, *c, out, @a, @o_idx, @c_idx); true);
        }
        None => panic!(),
    }

    out
}

// OK
#[cfg_attr(all(any(trust_conflict, trust_all), not(untrust_all)), trusted)]
#[requires(trail.invariant(*_f))]
#[requires(c.unsat(trail.assignments))]
#[requires(@i <= (@trail.trail).len())]
#[requires((@trail.trail).len() > 0)]
#[ensures(match result {
    Some(r) =>  @r < (@c).len()
                && (@c)[@r].is_opp((@trail.trail)[@^i].lit)
                && (@c)[@r].idx === (@trail.trail)[@^i].lit.idx,
    None => true
})]
#[ensures(@^i < (@trail.trail).len())]
fn choose_literal(c: &Clause, trail: &Trail, i: &mut usize, _f: &Formula) -> Option<usize> {
    let old_i = Ghost::record(&i);
    #[invariant(i_bound, 0 <= @i && @i <= (@trail.trail).len())]
    #[invariant(proph_i, ^i === ^@old_i)]
    while *i > 0 {
        *i -= 1;
        let mut k: usize = 0;
        #[invariant(i_bound2, 0 <= @i && @i < (@trail.trail).len())]
        #[invariant(k_bound, 0 <= @k && @k <= (@c).len())]
        #[invariant(proph_i2, ^i === ^@old_i)]
        while k < c.rest.len() {
            if trail.trail[*i].lit.idx == c.rest[k].idx {
                return Some(k);
            }
            k += 1;
        }
    }
    None
}

#[cfg_attr(all(any(trust_conflict, trust_all), not(untrust_all)), trusted)]
//#[trusted] // OK
//#[requires(trail.trail_sem_invariant(*f, *a))]
//#[requires(a.invariant(*f))]
#[requires(f.invariant())]
#[requires(trail.invariant(*f))]
#[requires((@trail.decisions).len() > 0)]
#[requires((@trail.trail).len() > 0)]
#[requires(@cref < (@f.clauses).len())]
#[requires((@f.clauses)[@cref].unsat(trail.assignments))]
#[ensures(match result {
    //Conflict::Ground => f.unsat(*a), // Either have to do proof on this seperately or reforumlate
    Conflict::Unit(lit) => {0 <= @lit.idx && @lit.idx < (@trail.assignments).len()}, // know lit can be learned
    Conflict::Learned(level, lit, clause) => {
        //@level > 0 && @level <= (@trail.trail).len() && // Don't need atm
        @lit.idx < (@trail.assignments).len() && // can be changed to lit in or somet
        (@clause).len() > 1 &&
        vars_in_range_inner(@clause, @f.num_vars) &&
        no_duplicate_indexes_inner(@clause) &&
        equisat_extension_inner(clause, @f)
    }, 
    _ => { true }
})]
pub fn analyze_conflict(f: &Formula, trail: &Trail, cref: usize) -> Conflict {
    let decisionlevel = trail.decision_level();
    if decisionlevel == 0 {
        return Conflict::Ground;
    }
    let mut i = trail.trail.len();
    let mut clause = f.clauses[cref].clone();
    #[invariant(clause_vars, clause.invariant_unary_ok(@f.num_vars))]
    #[invariant(clause_equi, equisat_extension_inner(clause, @f))]
    #[invariant(clause_unsat, clause.unsat(trail.assignments))]
    #[invariant(clause_len, (@clause).len() > 0)]
    #[invariant(i_bound, 0 <= @i && @i <= (@trail.trail).len())]
    while i > 0 {
        let c_idx = match choose_literal(&clause, trail, &mut i, f) {
            None => return Conflict::Panic,
            Some(b) => b,
        };
                
        let ante = match &trail.trail[i].reason {
            Reason::Long(c) => &f.clauses[*c],
            o => {return Conflict::Panic}, // nnTODOnn // This never happens, but is an entirely new proof
        };
        clause = resolve(f, &clause, &ante, trail.trail[i].lit.idx, c_idx, &trail.assignments);
        let mut k: usize = 0;
        let mut cnt: usize = 0;
        #[invariant(k_bound, @k <= (@clause.rest).len())]
        #[invariant(cnt_bound, @cnt <= @k)]
        while k < clause.rest.len() {
            if trail.lit_to_level[clause.rest[k].idx] == decisionlevel {
                cnt += 1;
            }
            k += 1;
        }
        if cnt == 1 {
            break;
        }
    }
    // TODO: Get level and return asserting level

    if clause.rest.len() == 1 {
        Conflict::Unit(clause.rest[0])
    } else {
        Conflict::Learned(cref, clause.rest[0], clause)
    }
}
