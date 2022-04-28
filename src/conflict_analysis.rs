extern crate creusot_contracts;
use creusot_contracts::std::*;
use creusot_contracts::*;

use crate::{assignments::*, clause::*, formula::*, lit::*, trail::*};

#[cfg(feature = "contracts")]
use crate::logic::{logic::*, logic_clause::*, logic_conflict_analysis::*, logic_formula::*};

//#[derive(Debug)]
pub enum Conflict {
    Ground,
    Unit(Clause),
    //Learned(usize, Lit, Vec<Lit>),
    Learned(usize, Clause),
    Panic,
}

#[cfg_attr(feature = "trust_conflict", trusted)]
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

#[cfg_attr(feature = "trust_conflict", trusted)]
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
#[requires(o.post_unit_inner(@_a))]
#[requires(c.unsat_inner(@_a))]
#[requires(c.invariant(@_f.num_vars))]
#[requires(o.invariant(@_f.num_vars))]
#[ensures(result.unsat_inner(@_a))]
#[ensures(result.invariant(@_f.num_vars))]
#[ensures(result.vars_in_range(@_f.num_vars))]
#[ensures(equisat_extension_inner(result, @_f))]
//#[ensures((@result).len() > 0)] // TODO: Need to prove this
// Okay so to prove the length, we have to prove that the resolved clause is at minimum the length of the
// the second clause - 1, which is a long, and all longs are at least of length 2(this should be made an invariant if
// it isnt already)
// Requires long(o)
//#[ensures((@result).len() >= (@o).len() - 1)] // TODO: Need to prove this
//#[ensures((@result).len() >= (@c).len() - 1)] // TODO: Need to prove this
fn resolve(
    _f: &Formula,
    c: &Clause,
    o: &Clause,
    idx: usize,
    c_idx: usize,
    _a: &Assignments,
) -> Clause {
    let mut new: Vec<Lit> = Vec::new();
    let mut i: usize = 0;
    #[invariant(i_less, @i <= (@c.rest).len())]
    #[invariant(new_elems, forall<j: Int> 0 <= j && j < (@new).len() ==>
        (@new)[j].invariant(@_f.num_vars))]
    #[invariant(no_dups, forall<j: Int, k: Int> 0 <= j && j < (@new).len() && 0 <= k && k < j ==>
        @(@new)[j].idx != @(@new)[k].idx)]
    #[invariant(not_idx, forall<j: Int> 0 <= j && j < (@new).len() ==> @(@new)[j].idx != @idx)]
    #[invariant(reso, forall<j: Int> 0 <= j && j < @i && @(@c)[j].idx != @idx ==>
        (@c)[j].lit_in_internal(@new) && true && true && true)]
    #[invariant(from_c, forall<j: Int> 0 <= j && j < (@new).len() ==> (@new)[j].lit_in(*c))]
    while i < c.rest.len() {
        let old_new = Ghost::record(&new);
        if c.rest[i].idx == idx {
            proof_assert!(@new === @@old_new);
            proof_assert!(@(@c)[@i].idx == @idx);
            proof_assert!(forall<j: Int> 0 <= j && j < @i && @(@c)[j].idx != @idx ==>
            (@c)[j].lit_in_internal(@new));
        } else if idx_in(&new, c.rest[i].idx) {
            proof_assert!(@new === @@old_new);
            proof_assert!((@c)[@i].lit_in_internal(@new));
            proof_assert!(@(@c)[@i].idx != @idx);
            proof_assert!(forall<j: Int> 0 <= j && j < @i && @(@c)[j].idx != @idx ==>
            (@c)[j].lit_in_internal(@new));
        } else {
            new.push(c.rest[i]);
            proof_assert!((@new)[(@new).len() - 1] === (@c.rest)[@i]);
            proof_assert!((@new)[(@new).len() - 1].lit_in(*c));
            proof_assert!((@c)[@i].lit_in_internal(@new));
            proof_assert!(@(@c)[@i].idx != @idx);
            proof_assert!(forall<j: Int> 0 <= j && j < @i && @(@c)[j].idx != @idx ==>
            (@c)[j].lit_in_internal(@new));
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
        (@c)[j].lit_in_internal(@new) && true))]
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
    let out = Clause { deleted: false, rest: new };
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

/*
// Started on this, but can't be bothered finishing it now
// So the great thing is that this seems to not be any faster?
#[cfg_attr(all(any(trust_conflict, trust_all), not(untrust_all)), trusted)]
#[requires(_f.invariant())]
#[requires(equisat_extension_inner(*c, @_f))]
#[ensures(equisat_extension_inner(^c, @_f))]
#[maintains((mut c).unsat_inner(@_a))]
#[maintains((mut c).invariant_unary_ok(@_f.num_vars))]
#[maintains((mut c).vars_in_range(@_f.num_vars))]
#[requires(o.in_formula(*_f))]
#[requires(@c_idx < (@c).len() && @(@c)[@c_idx].idx === @idx &&
    (exists<k: Int> 0 <= k && k < (@o).len() &&
        (@o)[k].is_opp((@c)[@c_idx]))
)]
#[requires(forall<j: Int, k: Int> 0 <= j && j < (@o).len() && 0 <= k && k < (@c).len() &&
    k != @c_idx && @(@o)[j].idx != @idx ==> !(@c)[k].is_opp((@o)[j]))]
#[requires(c.same_idx_same_polarity_except(*o, @idx))]
#[requires(@idx < @_f.num_vars)]
#[requires(o.post_unit_inner(@_a))]
#[requires(o.invariant_unary_ok(@_f.num_vars))]
#[ensures((@c).len() > 0)] // TODO: Need to prove this
fn resolve_mut(_f: &Formula, c: &mut Clause, o: &Clause, idx: usize, c_idx: usize, _a: &Assignments) {
    let mut i: usize = 0;
    let old_c = Ghost::record(&c);
    c.remove_from_clause(c_idx, _f);
    proof_assert!(forall<j: Int> 0 <= j && j < (@c).len() ==>
        (@c)[j].invariant(@_f.num_vars));
    proof_assert!(forall<j: Int, k: Int> 0 <= j && j < (@c).len() && 0 <= k && k < j ==>
        @(@c)[j].idx != @(@c)[k].idx);
    proof_assert!(forall<j: Int> 0 <= j && j < (@c).len() ==> @(@c)[j].idx != @idx); // TODO on this one
    proof_assert!(forall<j: Int> 0 <= j && j < @i && @(@@old_c)[j].idx != @idx ==>
        (@@old_c)[j].lit_in_internal(@c));
    proof_assert!(forall<j: Int> 0 <= j && j < (@c).len() ==> (@c)[j].lit_in(*c));
    proof_assert!(forall<j: Int> 0 <= j && j < @i && j != @c_idx ==>
        (@@old_c)[j].lit_in_internal(@c));
    proof_assert!(^@old_c === ^c);
    /*
    while i < o.rest.len() {
        if idx_in(&c.rest, o.rest[i].idx) {
        } else if o.rest[i].idx == idx {
        } else {
            c.rest.push(o.rest[i]);
        }
        i += 1;
    }
    */
}
*/

// OK
#[cfg_attr(feature = "trust_conflict", trusted)]
#[requires(trail.invariant(*_f))]
#[requires(c.unsat(trail.assignments))]
#[requires(@i <= (@trail.trail).len())] // not needed?
#[requires((@trail.trail).len() > 0)] // Do I really need this?
#[ensures(match result {
    Some(r) =>  @r < (@c).len()
                && (@c)[@r].is_opp((@trail.trail)[@^i].lit)
                && (@c)[@r].idx === (@trail.trail)[@^i].lit.idx
                //&& c.same_idx_same_polarity_except(*o, @r)
                ,
    None => true
})]
#[ensures(@^i < (@trail.trail).len())] // Not needed?
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

// TODO
// Had to add swapping to make vmtf work. Need to prove that swapping is fine.
// Probably gonna restore old analyze_conflict and move it out.
// (in other words gonna make a function make_asserting_clause() from
// equisat clause to equisat clause)
#[cfg_attr(feature = "trust_conflict", trusted)]
#[requires(f.invariant())]
#[requires(trail.invariant(*f))]
#[requires(@cref < (@f.clauses).len())]
#[requires((@f.clauses)[@cref].unsat(trail.assignments))]
#[ensures(match result {
    Conflict::Ground => f.not_satisfiable(),
    Conflict::Unit(clause) => {
        clause.invariant(@f.num_vars)
        && (@clause).len() == 1
        && vars_in_range_inner(@clause, @f.num_vars)
        && no_duplicate_indexes_inner(@clause)
        && equisat_extension_inner(clause, @f)
    },
    Conflict::Learned(level, clause) => {
        clause.invariant(@f.num_vars)
        && @level < (@trail.decisions).len() //added
        && (@clause).len() > 1
        && vars_in_range_inner(@clause, @f.num_vars)
        && no_duplicate_indexes_inner(@clause)
        && equisat_extension_inner(clause, @f)
    },
    _ => { true }
})]
#[ensures(match result {
    Conflict::Ground => (@trail.decisions).len() === 0,
    Conflict::Panic  => true,
    _                => {(@trail.decisions).len() > 0 },
})]
pub fn analyze_conflict(f: &Formula, trail: &Trail, cref: usize) -> Conflict {
    let decisionlevel = trail.decision_level();
    if decisionlevel == 0 {
        return match derive_empty_formula(f, trail, cref) {
            true => Conflict::Ground,
            false => Conflict::Panic,
        };
    }
    let mut i = trail.trail.len();
    let mut clause = f.clauses[cref].clone();
    let mut s_idx: usize = 0;
    #[invariant(clause_vars, clause.invariant_unary_ok(@f.num_vars))]
    #[invariant(clause_equi, equisat_extension_inner(clause, @f))]
    #[invariant(clause_unsat, clause.unsat(trail.assignments))]
    //#[invariant(clause_len, (@clause).len() > 0)]
    #[invariant(i_bound, 0 <= @i && @i <= (@trail.trail).len())]
    while i > 0 {
        proof_assert!((@trail.trail).len() > 0);
        let c_idx = match choose_literal(&clause, trail, &mut i, f) {
            None => return Conflict::Panic,
            Some(b) => b,
        };
        proof_assert!(@i < (@trail.trail).len());
        let ante = match &trail.trail[i].reason {
            Reason::Long(c) => &f.clauses[*c],
            o => return Conflict::Panic, // nnTODOnn // This never happens, but is an entirely new proof
        };
        proof_assert!(clause.same_idx_same_polarity_except(*ante, @(@trail.trail)[@i].lit.idx));
        clause = resolve(
            f,
            &clause,
            &ante,
            trail.trail[i].lit.idx,
            c_idx,
            &trail.assignments,
        );
        //resolve_mut(f, &mut clause, &ante, trail.trail[i].lit.idx, c_idx, &trail.assignments);
        s_idx = 0;
        let mut k: usize = 0;
        let mut cnt: usize = 0;
        #[invariant(k_bound, @k <= (@clause.rest).len())]
        #[invariant(s_idx_ok, @s_idx <= @k)]
        #[invariant(cnt_bound, @cnt <= @k)]
        while k < clause.rest.len() {
            if trail.lit_to_level[clause.rest[k].idx] == decisionlevel {
                cnt += 1;
                if cnt > 1 {
                    break;
                }
                s_idx = k;
            }
            k += 1;
        }
        if cnt == 1 {
            clause.rest.swap(0, s_idx);
            break;
        }
    }
    if clause.rest.len() == 0 {
        return Conflict::Panic; // Okay this is just pure lazyness
    }

    if clause.rest.len() == 1 {
        Conflict::Unit(clause)
    } else {
        let mut max_i: usize = 1;
        let mut max_level = trail.lit_to_level[clause.rest[1].idx];
        i = 2;
        #[invariant(max_i_less, @max_i < (@clause.rest).len())]
        while i < clause.rest.len() {
            let level = trail.lit_to_level[clause.rest[i].idx];
            if level > max_level {
                max_level = level;
                max_i = i;
            }
            i += 1;
        }
        clause.rest.swap(1, max_i);
        Conflict::Learned(max_level, clause)
        //Conflict::Learned(0, clause)
    }
}

// Just analyze_conflict without a stopping condition(and with accepting units for resolution)
// OK
#[cfg_attr(feature = "trust_conflict", trusted)]
#[requires(f.invariant())]
#[requires(trail.invariant(*f))]
#[requires(@cref < (@f.clauses).len())]
#[requires((@f.clauses)[@cref].unsat(trail.assignments))]
#[ensures(match result {
    true  => f.not_satisfiable(),
    false => true,
})]
pub fn derive_empty_formula(f: &Formula, trail: &Trail, cref: usize) -> bool {
    let mut i = trail.trail.len();
    let mut clause = f.clauses[cref].clone();
    #[invariant(clause_vars, clause.invariant_unary_ok(@f.num_vars))]
    #[invariant(clause_equi, equisat_extension_inner(clause, @f))]
    #[invariant(clause_unsat, clause.unsat(trail.assignments))]
    #[invariant(clause_len, (@clause).len() > 0)]
    #[invariant(i_bound, 0 <= @i && @i <= (@trail.trail).len())]
    while i > 0 {
        proof_assert!((@trail.trail).len() > 0);
        let c_idx = match choose_literal(&clause, trail, &mut i, f) {
            None => return false,
            Some(b) => b,
        };
        proof_assert!(@i < (@trail.trail).len());
        let ante = match &trail.trail[i].reason {
            Reason::Long(c) => &f.clauses[*c],
            Reason::Unit(c) => &f.clauses[*c],
            o => return false, // nnTODOnn // This never happens, but is an entirely new proof
        };
        proof_assert!(clause.same_idx_same_polarity_except(*ante, @(@trail.trail)[@i].lit.idx));
        clause = resolve(
            f,
            &clause,
            &ante,
            trail.trail[i].lit.idx,
            c_idx,
            &trail.assignments,
        );
        //resolve_mut(f, &mut clause, &ante, trail.trail[i].lit.idx, c_idx, &trail.assignments);
        if clause.rest.len() == 0 {
            return true;
        }
    }
    return false;
}
