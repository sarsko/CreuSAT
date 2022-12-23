extern crate creusot_contracts;
use creusot_contracts::{std::*, Ghost, *};

use crate::{assignments::*, clause::*, decision::*, formula::*, lit::*, trail::*};

#[cfg(feature = "contracts")]
use crate::logic::{
    logic::*, logic_clause::*, logic_conflict_analysis::*, logic_formula::*, logic_lit::*, logic_util::*,
};

//#[derive(Debug)]
pub enum Conflict {
    Ground,
    Unit(Clause),
    Learned(usize, Clause),
    Restart(Clause), // This is an error state when we derive a non-asserting clause
}

#[inline(always)]
#[cfg_attr(feature = "trust_conflict", trusted)]
#[requires(vars_in_range_inner(@c, (@seen).len()))]
#[requires(@idx < (@seen).len())]
#[requires((@seen)[@idx] == idx_in_logic(@idx, @c))]
#[ensures(result == (exists<i: Int> 0 <= i && i < (@c).len() && (@c)[i].index_logic() == @idx))]
fn idx_in(c: &Vec<Lit>, idx: usize, seen: &Vec<bool>) -> bool {
    seen[idx]
}

#[cfg_attr(feature = "trust_conflict", trusted)]
#[requires(_f.invariant())]
#[requires(trail.invariant(*_f))]
#[requires(@idx < @_f.num_vars)]
#[requires(o.in_formula(*_f))]
#[requires(@c_idx < (@c).len()
    && (@c)[@c_idx].index_logic() == @idx
    && (@o)[0].is_opp((@c)[@c_idx])
)]
#[requires(c.same_idx_same_polarity_except(*o, @idx))]
// New post unit -> abstract away
#[requires(forall<j: Int> 1 <= j && j < (@o).len() ==> (@o)[j].unsat_inner(@trail.assignments))]
#[requires((@o)[0].sat_inner(@trail.assignments))]
#[requires(@path_c > 0 && @path_c <= (@c).len())]
#[ensures(@^path_c <= (@^c).len())]
// Maintains:
#[requires((@seen).len() == @_f.num_vars)]
#[ensures((@^seen).len() == @_f.num_vars)]
#[requires(elems_less_than(@to_bump, @_f.num_vars))]
#[ensures(elems_less_than(@^to_bump, @_f.num_vars))]
#[maintains(equisat_extension_inner(mut c, @_f))]
#[maintains((mut c).clause_is_seen(mut seen))]
#[maintains((mut c).unsat(trail.assignments))] // TODO: Should be stated with regards to seq
#[maintains((mut c).invariant(@_f.num_vars))]
fn resolve(
    _f: &Formula, c: &mut Clause, o: &Clause, idx: usize, c_idx: usize, trail: &Trail, seen: &mut Vec<bool>,
    path_c: &mut usize, to_bump: &mut Vec<usize>,
) {
    let old_c: Ghost<&mut Clause> = ghost!(c);
    let old_seen: Ghost<&mut Vec<bool>> = ghost!(seen);
    let old_path_c: Ghost<&mut usize> = ghost!(path_c);
    let old_to_bump: Ghost<&mut Vec<usize>> = ghost!(to_bump);

    proof_assert!(c.clause_is_seen(*seen));

    c.remove_from_clause(c_idx, _f);

    *path_c -= 1;
    seen[idx] = false;

    proof_assert!(^seen == ^old_seen.inner());
    proof_assert!(c.clause_is_seen(*seen));
    let old_c2: Ghost<&mut Clause> = ghost!(c);
    proof_assert!(!(@old_c)[@c_idx].lit_in(*c));
    proof_assert!(^c == ^old_c.inner());
    proof_assert!(forall<j: Int> 0 <= j && j < (@old_c).len()
        && j != @c_idx ==> (@old_c)[j].lit_in(*c));

    // Add all the literals from the other clause
    let mut i: usize = 1;
    #[invariant(inv, c.invariant(@_f.num_vars))]
    #[invariant(all_unsat, c.unsat(trail.assignments))] // TODO: Should be stated with regards to seq
    #[invariant(i_bound, 1 <= @i && @i <= (@o).len())]
    #[invariant(not_in, !(@old_c)[@c_idx].lit_in(*c) && !(@o)[0].lit_in(*c))]
    #[invariant(all_in, forall<j: Int> 1 <= j && j < @i ==> (@o)[j].lit_in(*c))]
    #[invariant(all_in2, forall<j: Int> 0 <= j && j < (@old_c).len()
        && j != @c_idx ==> (@old_c)[j].lit_in(*c))]
    #[invariant(from_c_or_o, (forall<j: Int> 0 <= j && j < (@c).len() ==>
                    ((@c)[j].lit_in(*old_c.inner()) ||  (@c)[j].lit_in(*o))))]
    #[invariant(path_c_less, @path_c <= (@c).len())]
    #[invariant(seen_is_clause, c.clause_is_seen(*seen))]
    #[invariant(seen_len, (@seen).len() == @_f.num_vars)]
    #[invariant(elems_less, elems_less_than(@to_bump, @_f.num_vars))]
    #[invariant(proph_c, ^c == ^old_c.inner())]
    #[invariant(proph_seen, ^seen == ^old_seen.inner())]
    #[invariant(proph_path_c, ^path_c == ^old_path_c.inner())]
    #[invariant(proph_to_bump, ^to_bump == ^old_to_bump.inner())]
    while i < o.len() {
        let old_c3: Ghost<&mut Clause> = ghost!(c);
        proof_assert!(^c == ^old_c3.inner());

        if !idx_in(&c.lits, o[i].index(), &seen) {
            seen[o[i].index()] = true;
            to_bump.push(o[i].index());
            c.lits.push(o[i]);
            if trail.lit_to_level[o[i].index()] >= trail.decision_level() {
                *path_c += 1;
            }
            proof_assert!(@c == (@old_c3).push((@o)[@i]));
            proof_assert!((@c).len() == (@old_c3).len() + 1);
            proof_assert!((@o)[@i].lit_in(*c));
        }

        proof_assert!(forall<j: Int> 0 <= j && j < (@old_c3).len() ==>
            ((@old_c3)[j] == (@c)[j]));
        i += 1;
    }
    proof_assert!(c.resolvent_of(*old_c.inner(), *o, 0, @c_idx));
    proof_assert!(lemma_resolvent_of_equisat_extension_is_equisat(@_f, *old_c.inner(), *o, *c, @c_idx, 0);true);
}

#[cfg_attr(feature = "trust_conflict", trusted)]
#[requires(trail.invariant(*_f))]
#[requires(c.unsat(trail.assignments))]
#[requires(@i <= (@trail.trail).len())]
#[requires((@seen).len() == @_f.num_vars)]
#[ensures(match result {
    Some(r) =>  @r < (@c).len()
                && (@c)[@r].is_opp((@trail.trail)[@^i].lit)
                && (@c)[@r].index_logic() == (@trail.trail)[@^i].lit.index_logic()
                && @^i < (@trail.trail).len()
                //&& c.same_idx_same_polarity_except(*o, @r)
                ,
    None => @^i == 0
})]
fn choose_literal(c: &Clause, trail: &Trail, i: &mut usize, _f: &Formula, seen: &Vec<bool>) -> Option<usize> {
    let old_i: Ghost<&mut usize> = ghost! {i};
    #[invariant(i_bound, 0 <= @i && @i <= (@trail.trail).len())]
    #[invariant(proph_i, ^i == ^old_i.inner())]
    while *i > 0 {
        *i -= 1;
        if seen[trail.trail[*i].lit.index()] {
            let mut k: usize = 0;
            #[invariant(i_bound2, 0 <= @i && @i < (@trail.trail).len())]
            #[invariant(k_bound, 0 <= @k && @k <= (@c).len())]
            #[invariant(proph_i2, ^i == ^old_i.inner())]
            while k < c.len() {
                if trail.trail[*i].lit.index() == c[k].index() {
                    return Some(k);
                }
                k += 1;
            }
        }
    }
    None
}

#[cfg_attr(feature = "trust_conflict", trusted)]
#[requires(f.invariant())]
#[requires(@f.num_vars < @usize::MAX)]
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
    Conflict::Learned(s_idx, clause) => {
        clause.invariant(@f.num_vars)
        && (@clause).len() > 1
        && vars_in_range_inner(@clause, @f.num_vars)
        && no_duplicate_indexes_inner(@clause)
        && equisat_extension_inner(clause, @f)
        && @s_idx < (@clause).len()
    },
    Conflict::Restart(clause) => {
        clause.invariant(@f.num_vars)
        && (@clause).len() > 1
        && vars_in_range_inner(@clause, @f.num_vars)
        && no_duplicate_indexes_inner(@clause)
        && equisat_extension_inner(clause, @f)
    },
})]
#[maintains((mut d).invariant(@f.num_vars))]
pub fn analyze_conflict(f: &Formula, trail: &Trail, cref: usize, d: &mut Decisions) -> Conflict {
    let decisionlevel = trail.decision_level();
    let mut to_bump = Vec::new();
    let break_cond = if decisionlevel == 0 { 0 } else { 1 };
    let mut path_c: usize = 0;
    let mut seen = vec![false; f.num_vars];
    let mut i = trail.trail.len();
    let clause = f[cref].clone();
    let mut j: usize = 0;
    #[invariant(seen_is_clause, forall<idx: Int> 0 <= idx && idx < (@seen).len() ==>
        ((@seen)[idx] == (exists<i: Int> 0 <= i && i < @j && (@clause)[i].index_logic() == idx)))]
    #[invariant(seen_len, (@seen).len() == @f.num_vars)]
    #[invariant(path_c_less, @path_c <= @j)]
    #[invariant(j_is_len, @j <= (@clause).len())] // This is needed to establish the loop invariant for the next loop
    #[invariant(elems_less, elems_less_than(@to_bump, @f.num_vars))]
    while j < clause.len() {
        seen[clause[j].index()] = true;
        to_bump.push(clause[j].index());
        if trail.lit_to_level[clause[j].index()] >= decisionlevel {
            path_c += 1;
        }
        j += 1;
    }
    let mut clause = clause;
    #[invariant(seen_len, (@seen).len() == @f.num_vars)]
    #[invariant(seen_is_clause, forall<idx: Int> 0 <= idx && idx < (@seen).len() ==>
        ((@seen)[idx] == idx_in_logic(idx, @clause)))]
    #[invariant(clause_vars, clause.invariant(@f.num_vars))]
    #[invariant(clause_equi, equisat_extension_inner(clause, @f))]
    #[invariant(clause_unsat, clause.unsat(trail.assignments))]
    #[invariant(i_bound, 0 <= @i && @i <= (@trail.trail).len())]
    #[invariant(path_c_less, @path_c <= (@clause).len())]
    #[invariant(elems_less, elems_less_than(@to_bump, @f.num_vars))]
    while path_c > break_cond {
        let c_idx = match choose_literal(&clause, trail, &mut i, f, &seen) {
            Some(c_idx) => c_idx,
            None => break,
        };
        let ante = match &trail.trail[i].reason {
            Reason::Long(c) => &f[*c],
            Reason::Unit(c) => &f[*c],
            _ => break,
        };
        let idx = trail.trail[i].lit.index();
        proof_assert!(clause.same_idx_same_polarity_except(*ante, @idx));
        resolve(f, &mut clause, ante, idx, c_idx, &trail, &mut seen, &mut path_c, &mut to_bump);
    }
    //let clause = clause;
    d.increment_and_move(f, to_bump);
    if clause.len() == 0 {
        Conflict::Ground
    } else if clause.len() == 1 {
        Conflict::Unit(clause)
    } else {
        //clause.search = 2; // Setting this breaks equisat extension
        if path_c > break_cond {
            return Conflict::Restart(clause);
        }
        let mut k: usize = 0;
        let mut s_idx: usize = 0;
        #[invariant(k_bound, @k <= (@clause).len())]
        #[invariant(s_idx_ok, @s_idx < (@clause).len())]
        while k < clause.len() {
            if trail.lit_to_level[clause[k].index()] == decisionlevel {
                s_idx = k;
                break;
            }
            k += 1;
        }
        Conflict::Learned(s_idx, clause)
    }
}

#[cfg_attr(feature = "trust_conflict", trusted)]
#[requires(f.invariant())]
#[requires(trail.invariant(*f))]
#[requires(@cref < (@f.clauses).len())]
#[requires((@f.clauses)[@cref].unsat(trail.assignments))]
#[ensures(result ==> f.not_satisfiable())]
pub fn resolve_empty_clause(f: &Formula, trail: &Trail, cref: usize) -> bool {
    let decisionlevel = trail.decision_level();
    let mut seen = vec![false; f.num_vars];
    let mut i = trail.trail.len();
    let clause = f[cref].clone();
    let mut to_bump = Vec::new();
    let mut j: usize = 0;
    #[invariant(seen_is_clause, forall<idx: Int> 0 <= idx && idx < (@seen).len() ==>
        ((@seen)[idx] == (exists<i: Int> 0 <= i && i < @j && (@clause)[i].index_logic() == idx)))]
    #[invariant(seen_len, (@seen).len() == @f.num_vars)]
    #[invariant(j_is_len, @j <= (@clause).len())]
    // This is needed to establish the loop invariant for the next loop
    while j < clause.len() {
        seen[clause[j].index()] = true;
        j += 1;
    }
    let mut clause = clause;
    proof_assert!(clause.clause_is_seen(seen));
    let c_idx = match choose_literal(&clause, trail, &mut i, f, &seen) {
        Some(c_idx) => c_idx,
        None => return false,
    };
    let ante = match &trail.trail[i].reason {
        //Reason::Long(c) => &f.clauses[*c],
        Reason::Unit(c) => &f[*c],
        _ => return false,
    };
    let mut path_c = 1;
    resolve(f, &mut clause, ante, trail.trail[i].lit.index(), c_idx, &trail, &mut seen, &mut path_c, &mut to_bump);
    if clause.len() == 0 {
        return true;
    } else {
        return false;
    }
}
