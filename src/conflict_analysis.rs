extern crate creusot_contracts;
use creusot_contracts::*;
use creusot_contracts::std::*;

use crate::assignments::*;
use crate::clause::*;
use crate::formula::*;
use crate::lit::*;
use crate::trail::*;
//use crate::watches::*;
use crate::trail::{Reason::*};
use crate::logic::*;

//#[derive(Debug)]
pub enum Conflict {
    Ground,
    Unit(Lit),
    //Learned(usize, Lit, Vec<Lit>),
    Learned(usize, Lit, Clause),
    Panic,
}
/*
#[logic]
#[variant(j-i)]
fn count(i: Int, j: Int, t: Seq<Lit>, lf: Int) -> Int {
    pearlite! {
        if i >= j { 0 } else {
            if @t[j-1].idx === lf {
                count(i,j-1,t, lf) + 1
            } else {
                count(i,j-1,t, lf)
            }
        }
    }
}
*/

/*
#[logic]
#[requires(no_duplicate_indexes_inner(v))]
#[requires(v.permutation_of(v2))]
#[ensures(no_duplicate_indexes_inner(v2))]
fn lemma_no_dups_permut(v: Seq<Lit>, v2: Seq<Lit>) {}
*/

/*
#[requires(vars_in_range_inner(@v, @_f.num_vars))]
#[requires(no_duplicate_indexes_inner(@v))]
#[requires(@to_be_removed < (@v).len())]
#[ensures((@^v).permutation_of(@v))]
#[ensures(vars_in_range_inner(@^v, @_f.num_vars))]
#[ensures(no_duplicate_indexes_inner(@^v))]
#[ensures((@v).len() === (@^v).len() + 1)]
fn move_to_end(v: &mut Vec<Lit>, to_be_removed: usize,  _f: &Formula) {
    let end = v.len() - 1;
    v.swap(to_be_removed, end);
    //v.pop();
}
*/
#[trusted] // OK
#[logic]
//#[requires(@v[i].idx === idx)]
#[requires(0 <= c_idx && c_idx < c.len() && @(c)[c_idx].idx === idx &&
    (exists<k: Int> 0 <= k && k < o.len() && k != i &&
        o[k].is_opp(c[c_idx]))
)]
#[requires(forall<j: Int, k: Int> 0 <= j && j < o.len() && 0 <= k && k < c.len() &&
    k != c_idx && @o[j].idx != idx ==> !c[k].is_opp((o)[j]))]
#[requires(0 <= i && i < o.len() && @o[i].idx != idx)]
#[requires(invariant_internal(o, @_f.num_vars))]
#[requires(invariant_internal(c, @_f.num_vars))]
#[requires(forall<j: Int> 0 <= j && j < c.len() && @c[j].idx != idx ==> c[j].lit_in_internal(new))]
#[requires(forall<j: Int> 0 <= j && j < new.len() ==> (new)[j].lit_in_internal(c) || (new)[j].lit_in_internal(o))]
#[requires(exists<k: Int> 0 <= k && k < new.len() && @o[i].idx === @(new)[k].idx)]
#[ensures(exists<k: Int> 0 <= k && k < c.len() && @o[i].idx === @c[k].idx || (o)[i].lit_in_internal(new))]
#[ensures(exists<k: Int> 0 <= k && k < c.len() && @o[i].idx === @c[k].idx && o[i].polarity === c[k].polarity || (o)[i].lit_in_internal(new))]
//#[ensures(((o)[i].lit_in_internal(new)))]
fn lemma_idx(c: Seq<Lit>, o: Seq<Lit>, new: Seq<Lit>, i: Int, idx: Int, c_idx: Int, _f: Formula) {}

#[trusted] // OK
#[logic]
//#[requires(@v[i].idx === idx)]
#[requires(0 <= c_idx && c_idx < c.len() && @(c)[c_idx].idx === idx &&
    (exists<k: Int> 0 <= k && k < o.len() && k != i &&
        o[k].is_opp(c[c_idx]))
)]
#[requires(forall<j: Int, k: Int> 0 <= j && j < o.len() && 0 <= k && k < c.len() &&
    k != c_idx && @o[j].idx != idx ==> !c[k].is_opp((o)[j]))]
#[requires(0 <= i && i < o.len() && @o[i].idx != idx)]
#[requires(invariant_internal(o, @_f.num_vars))]
#[requires(invariant_internal(c, @_f.num_vars))]
#[requires(forall<j: Int> 0 <= j && j < c.len() && @c[j].idx != idx ==> c[j].lit_in_internal(new))]
#[requires(forall<j: Int> 0 <= j && j < new.len() ==> (new)[j].lit_in_internal(c) || (new)[j].lit_in_internal(o))]
#[requires(exists<k: Int> 0 <= k && k < new.len() && @o[i].idx === @(new)[k].idx)]
#[ensures(((o)[i].lit_in_internal(new)))]
fn lemma_idx2(c: Seq<Lit>, o: Seq<Lit>, new: Seq<Lit>, i: Int, idx: Int, c_idx: Int, _f: Formula) {
    lemma_idx(c, o, new, i, idx, c_idx, _f);
}


#[trusted] // OK
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


// Assignments has to be passed in as we either have to have access to it
// in resolve, or we have to have access to the second resolve index outside of
// resolve. Can be lifted if watches and literal reordering gets implemented
// as we then have access to both resolve indexes everywhere.

#[trusted] // OK
//#[requires(equisat_extension_inner(*o, @_f))]
/*
#[requires(
    (exists<k: Int, m: Int> 0 <= k && k < (@o).len() && 0 <= m && m < (@c).len() &&
        @(@c)[m].idx === @idx && @(@o)[k].idx === @idx && (@o)[k].is_opp((@c)[m]))
)]
*/
#[requires(_f.invariant())]
#[requires(equisat_extension_inner(*c, @_f))]
#[requires(o.in_formula(*_f))]
#[requires(c.invariant(@_f.num_vars))]
#[requires(o.invariant(@_f.num_vars))]
#[requires(@c_idx < (@c).len() && @(@c)[@c_idx].idx === @idx &&
    (exists<k: Int> 0 <= k && k < (@o).len() &&
        (@o)[k].is_opp((@c)[@c_idx]))
)]
#[requires(forall<j: Int, k: Int> 0 <= j && j < (@o).len() && 0 <= k && k < (@c).len() &&
    k != @c_idx && @(@o)[j].idx != @idx ==> !(@c)[k].is_opp((@o)[j]))]
#[requires(c.same_idx_same_polarity_except(*o, @idx))]
#[requires(@idx < @_f.num_vars)]
#[ensures(result.invariant(@_f.num_vars))]
#[ensures(equisat_extension_inner(result, @_f))]

// resolved_post
#[requires(o.post_unit_inner(@_a))]
#[requires(c.invariant((@_a).len()))]
#[requires(o.invariant((@_a).len()))]
//#[requires((@c)[c_idx].sat_inner(@_a))]
#[requires(c.unsat_inner(@_a))]
//#[requires(0 <= c_idx && c_idx < (@c).len())]
//#[requires(0 <= c2_idx && c2_idx < (@c2).len())]
//#[requires(c3.resolvent_of(c, c2, c2_idx, c_idx))]
#[ensures(result.unsat_inner(@_a))]

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
            proof_assert!(o.invariant(@_f.num_vars));
            //proof_assert!(forall<j: Int> 0 <= j && j < (@c ).len() && @(@c )[j].idx != @idx ==> (@c )[j].lit_in_internal(@new));
            //proof_assert!(exists<k: Int> 0 <= k && k < (@c).len() && @(@o)[@i].idx === @(@c)[k].idx);
            proof_assert!(0 <= @i && @i < (@o).len() && @(@o)[@i].idx != @idx);
            proof_assert!(invariant_internal(@o, @_f.num_vars));
            proof_assert!(invariant_internal(@c, @_f.num_vars));
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
    proof_assert!(out.invariant(@_f.num_vars));

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

// Might end up doing this as an option. Time loss is really minimal, and it makes me not have to do
// a somewhat cumbersome proof.
// todo on result.1
#[trusted] // tmp
#[ensures(@result.0.idx < (@trail.vardata).len())]
//#[ensures(result.0.lit_in(*c))]
#[ensures(@result.1 < (@c).len())]
#[ensures(@(@c)[@result.1].idx === @result.0.idx)]
#[ensures((@c)[@result.1].is_opp(result.0))] // This will need a longer proof
// Super bad / simple

fn choose_literal(c: &Clause, trail: &Trail, i: &mut usize, j: &mut usize) -> (Lit, usize) {
    let (next, k) = {
        let mut k = 0;
        loop { 
            *j -= 1;
            k = 0;
            let mut broken = false;
            while k < c.rest.len() {
                if trail.trail[*i][*j].idx == c.rest[k].idx {
                    assert!(trail.trail[*i][*j].polarity != (c.rest[k]).polarity);
                    broken = true;
                    break;
                }
                k += 1;
            }
            if broken {
                break;
            }
            if *j == 0 {
                *i -= 1;
                *j = trail.trail[*i].len();
            }
        }
        (trail.trail[*i][*j], k)
    };
    (next, k)
}


// The "standard one" from Zha03
/*
check_ground();
cl = find_conflicting_clause();
loop {
    lit = choose_literal(cl);
    var = variable_of_literal(lit);
    ante = antecedent(var);
    cl = resolve(cl, ante, var);
    if stop_criterion_met(cl) {
        break;
    }
}
add_clause_to_database(cl);
back_dl = clause_asserting_level(cl);
return back_dl
*/
// Might also be good to do the proof of the extension being OK inside this rather than do
// a return then add
#[trusted] // OK 

#[requires(trail.trail_sem_invariant(*f, *a))]

#[requires(f.invariant())]
#[requires(a.invariant(*f))]
#[requires(trail.invariant(*f))]
#[requires((@trail.trail).len() > 0)]
#[requires(@cref < (@f.clauses).len())]
#[requires((@f.clauses)[@cref].unsat(*a))]
#[ensures(match result {
    //Conflict::Ground => f.unsat(*a), // Either have to do proof on this seperately or reforumlate
    Conflict::Unit(lit) => {true}, // know lit can be learned
    Conflict::Learned(level, lit, clause) => {
        //@level > 0 && @level <= (@trail.trail).len() && // Don't need atm
        @lit.idx < ((@a).len()) && // can be changed to lit in or somet
        (@clause).len() > 1 &&
        vars_in_range_inner(@clause, @f.num_vars) &&
        no_duplicate_indexes_inner(@clause) &&
        equisat_extension_inner(clause, @f)
    }, 
    _ => { true }
})]
pub fn analyze_conflict_new(f: &Formula, a: &Assignments, trail: &Trail, cref: usize) -> Conflict {
    let decisionlevel = trail.trail.len() - 1;
    if decisionlevel == 0 {
        return Conflict::Ground;
    }
    // Making these persistent is strictly speaking an optimization
    let mut i = trail.trail.len() - 1;
    let mut j = trail.trail[i].len();
    let mut clause = f.clauses[cref].clone();
    #[invariant(clause_ok, clause.invariant(@f.num_vars))]
    #[invariant(clause_equi, equisat_extension_inner(clause, @f))]
    #[invariant(clause_unsat, clause.unsat(*a))]
    loop {
    //i = trail.trail.len() - 1;
    //j = trail.trail[i].len();
        let (lit, c_idx) = choose_literal(&clause, trail, &mut i, &mut j);
        let ante = match &trail.vardata[lit.idx].1 {
            Long(c) => f.clauses[*c].clone(),
            o => return Conflict::Panic, // TODO // This never happens, but is an entirely new proof
            //o => panic!(),
        };
        //proof_assert!(exists<j: Int> 0 <= j && j < (@clause).len() && (@clause)[j].idx === lit.idx);
        //proof_assert!(exists<j: Int> 0 <= j && j < (@ante).len() && (@ante)[j].idx === lit.idx);
        proof_assert!(ante.post_unit(*a)); // Ensured by trail.vardata

        proof_assert!(exists<i: Int>
            0 <= i && i < (@ante).len() && @(@ante)[i].idx === @lit.idx && (@ante)[i].sat(*a)); // Also vardata
        proof_assert!(clause.unsat(*a)); // OK
        proof_assert!(lemma_same_pol(ante, clause, @a, @lit.idx);true);

        proof_assert!(clause.same_idx_same_polarity_except(ante, @lit.idx));
        proof_assert!(exists<k: Int> 0 <= k && k < (@ante).len() && (@ante)[k].is_opp((@clause)[@c_idx]));

        // Have to do the whole proof of conflict analysis.
        // Add precond that cref is a conflict clause and have to do proof that choose_lit
        // returns the conflicting literal. Then add the lemma that the clauses have no other opp lits
        // The good part is that we will get the backtracking level more or less for free
        
        clause = resolve(f, &clause, &ante, lit.idx, c_idx, a);
        let mut k: usize = 0;
        let mut cnt: usize = 0;
        #[invariant(k_bound, @k <= (@clause.rest).len())]
        #[invariant(cnt_bound, @cnt <= @k)]
        while k < clause.rest.len() {
            if trail.vardata[clause.rest[k].idx].0 == decisionlevel {
                cnt += 1;
            }
            k += 1;
        }
        if cnt == 1 {
            break;
        }
    }

    if clause.rest.len() == 1 {
        Conflict::Unit(clause.rest[0])
    } else {
        Conflict::Learned(cref, clause.rest[0], clause)
    }
}

#[trusted]
#[requires(f.invariant())]
#[requires(a.invariant(*f))]
#[requires(trail.invariant(*f))]
#[requires((@trail.trail).len() > 0)]
#[requires(@cref < (@f.clauses).len())]
#[ensures(match result {
    Conflict::Ground => f.unsat(*a),
    Conflict::Unit(lit) => {true}, // know lit can be learned
    Conflict::Learned(level, lit, clause) => {
        @level > 0 && @level <= (@trail.trail).len() &&
        @lit.idx < ((@a).len()) && // can be changed to lit in or somet
        (@clause).len() > 1 &&
        vars_in_range_inner(@clause, @f.num_vars) &&
        no_duplicate_indexes_inner(@clause) &&
        true
    }, // know clause can be learned
    _ => true,
})]
pub fn analyze_conflict(f: &Formula, a: &Assignments, trail: &Trail, cref: usize) -> Conflict {
    let decisionlevel = trail.trail.len() - 1;
    if decisionlevel == 0 {
        return Conflict::Ground;
    }
    // `seen` should be persistent across calls to `analyze_conflict`.
    // Solved by somehow keeping it in `solver`, either as a buffer or by making
    // conflict analysis a struct which is instatiated once and then kept.
    let mut seen = vec::from_elem(false, f.num_vars); //vec![false; f.num_vars]; 
    //let mut out_learnt = vec![Lit{idx: 999999, polarity: false}; 1]; // I really don't like this way of reserving space.
    let mut out_learnt = Vec::new();
    out_learnt.push(Lit{idx: 999999, polarity: false});

    let mut path_c = 0;
    let mut confl = cref;
    let mut i = trail.trail.len() - 1;
    let mut j = trail.trail[i].len();
    loop {
        let base = if confl == cref {0} else {1};
        let mut k = base;
        let clause = &f.clauses[confl].rest;
        while k < clause.len() {
            let lit = clause[k];
            if !seen[lit.idx] {
                let level = trail.vardata[lit.idx].0;
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
        let next = {
            loop { 
                j -= 1;
                if seen[trail.trail[i][j].idx] {
                    break;
                }
                if j == 0 {
                    i -= 1;
                    j = trail.trail[i].len();
                }
            }
            trail.trail[i][j]
        };
        seen[next.idx] = false;
        // now dlevel = i
        path_c -= 1;
        if path_c <= 0 {
            out_learnt[0] = !next;
            break;
        }
        match &trail.vardata[(!next).idx].1 {
            Long(c) => confl = *c,
            //other => panic!("Error - this has reason: {:?}", other),
            _other => panic!(),
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
        return Conflict::Learned(max_level, out_learnt[0], Clause{ rest: out_learnt });
    }
}