extern crate creusot_contracts;

use creusot_contracts::*;
use creusot_contracts::std::*;

use crate::assignments::*;
//use crate::clause::*;
use crate::formula::*;
use crate::lit::*;
use crate::trail::*;
use crate::watches::*;
use crate::trail::{Reason::*};

pub enum Conflict {
    Ground,
    Unit(Lit),
    Learned(usize, Lit, Vec<Lit>),
}
/*
#[logic]
#[variant(s.len()-i)]
#[requires(i >= 0 && i <= s.len())]
#[ensures(result >= 0)]
#[ensures(result === count_true_range(s, i, s.len()))]
fn count_true(s: Seq<bool>, i: Int) -> Int {
    count_true_range(s, i, s.len())
/*
    pearlite! {
        if i == s.len() { 0 }
        else { if s[i] {1 + count_true(s, i+1)
        } else { count_true(s, i+1) }}
    }
    */
}
*/

#[logic]
#[variant(j-i)]
//#[requires(i >= 0 && i <= s.len())]
//#[ensures(result >= 0 && result <= s.len())]
fn count_true_range(s: Seq<bool>, i: Int, j: Int) -> Int {
    pearlite! {
        if i >= j { 0 }
        else { if s[j-1] {count_true_range(s, i, j-1) + 1
        } else { count_true_range(s, i, j-1) }}
    }
}

#[logic]
#[requires(0 <= i && i < s.len())]
#[requires(s[i])]
#[ensures(count_true_range(s, 0, i) + 1 === count_true_range(s, 0, i+1))]
fn lemma_count_increases_with_true(s: Seq<bool>, i: Int) {}

#[logic]
#[requires(0 <= i && i < s.len())]
#[requires(!s[i])]
#[ensures(count_true_range(s, 0, i) === count_true_range(s, 0, i+1))]
fn lemma_count_does_not_increase_with_false(s: Seq<bool>, i: Int) {}

#[logic]
//#[requires(0 <= i && i < s.len())]
#[requires(forall<i: Int> 0 <= i && i < s.len() ==> !s[i])]
#[ensures(count_true_range(s, 0, s.len()) === 0)]
fn lemma_count_all_false_eq_zero(s: Seq<bool>) {
}

#[logic]
//#[requires(0 <= i && i < s.len())]
#[requires(count_true_range(s, 0, s.len()) === 0)]
#[ensures(forall<i: Int> 0 <= i && i < s.len() ==> !s[i])]
fn lemma_zero_implies_all_false(s: Seq<bool>, i: Int) {
    lemma_count_does_not_increase_with_false(s, 0);
    lemma_count_increases_with_true(s, 0);
}

/*
#[logic]
#[requires(j <= k)]
#[ensures(count_true_range(i,j,s) <= count_true_range(i,k,s))]
#[variant(k-j)]
fn lemma_num_of_pos_increasing(i: Int, j: Int, k: Int, s: Seq<bool>) {
    pearlite! {
        if j < k {
            lemma_num_of_pos_increasing(i,j+1,k,t)
        }
    }
}
*/

/*


#[logic]
#[requires(0 <= i && i < s.len())]
#[requires(s[i])]
#[ensures(count_true(s, i) === count_true(s, i+1) + 1)]
fn lemma_count_increases_with_true(s: Seq<bool>, i: Int) {}

#[logic]
#[requires(0 <= i && i < s.len())]
#[requires(!s[i])]
#[ensures(count_true(s, i) === count_true(s, i+1))]
fn lemma_count_does_not_increase_with_false(s: Seq<bool>, i: Int) {}
*/
/*
#[logic]
#[requires(forall<i: Int> 0 <= i && i < s.len() ==> !s[i])]
#[ensures(count_true(s, 0) === 0)]
fn lemma_count_all_false_eq_zero(s: Seq<bool>) {
    pearlite! {
        forall<j: Int> 0 <= j && j < s.len() ==>
        lemma_count_does_not_increase_with_false(s, j)
    };
}
*/

#[trusted]
#[requires(f.invariant())]
#[requires(a.invariant(@f.num_vars))]
#[requires(trail.invariant(*f))]
#[requires(_w.invariant(*f))]
#[requires(@f.num_vars < @usize::MAX/2)]
#[requires((@trail.trail).len() > 0)]
#[requires(@cref < (@f.clauses).len())]
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
pub fn analyze_conflict(f: &Formula, a: &Assignments, trail: &Trail, cref: usize, _w: &Watches) -> Conflict {
    let decisionlevel = trail.trail.len() - 1;
    if decisionlevel == 0 {
        return Conflict::Ground;
    }
    // `seen` should be persistent across calls to `analyze_conflict`.
    // Solved by somehow keeping it in `solver`, either as a buffer or by making
    // conflict analysis a struct which is instatiated once and then kept.
    //let mut num_true: usize = 0;
    //let mut seen: Vec<bool> = Vec::new();
    //slet mut k: usize = 0;
    /*
    #[invariant(seen_len, (@seen).len() === @k)]
    #[invariant(kbound, 0 <= @k && @k <= (@f.num_vars))]
    #[invariant(no_trues, 0 === count_true_range(@seen, 0, @k))]
    #[invariant(all_false, forall<i: Int> 0 <= i && i < @k ==> !(@seen)[i])]
    while k < f.num_vars {
        seen.push(false);
        k += 1;
        /*
        proof_assert! {
            lemma_count_does_not_increase_with_false(@seen, @k);
            count_true(@seen, @k) === count_true(@seen, @k - 1) &&
            count_true(@seen, 0) === 0
        }
        */
    }
    */
    let mut seen: Vec<bool> = vec::from_elem(false, f.num_vars);
    proof_assert! {
        lemma_count_all_false_eq_zero(@seen);
        count_true_range(@seen, 0, (@seen).len()) === 0
    }
    let mut out_learnt = Vec::new();
    out_learnt.push(Lit{idx: 0, polarity: false}); // I really don't like this way of reserving space.

    let mut path_c: usize = 0;
    let mut confl = cref;
    let mut i = trail.trail.len() - 1;
    let mut j = trail.trail[i].len();
    #[invariant(seen_same_len, (@seen).len() === @f.num_vars)]
    //#[invariant(pathc, @path_c <= @f.num_vars)]
    //#[invariant(pathc, @path_c <= count_true(@seen, 0))]
    #[invariant(pathc, @path_c <= count_true_range(@seen, 0, (@seen).len()))]
    #[invariant(iless, 0 <= @i && @i < (@trail.trail).len())]
    #[invariant(jless, 0 <= @j && @j <= (@(@trail.trail)[@i]).len())]
    #[invariant(out_learnt_len, (@out_learnt).len() >= 1)]
    #[invariant(out_learnt_ok, forall<m: Int> 0 <= m && m < (@out_learnt).len() ==>
        @(@out_learnt)[m].idx < @f.num_vars
    )]
    #[invariant(out_learnt_ok_trail, forall<m: Int> 0 <= m && m < (@out_learnt).len() ==>
        @(@trail.vardata)[@(@out_learnt)[m].idx].0 < (@trail.trail).len()
    )]
    #[invariant(confl_ok, @confl < (@f.clauses).len())]
    #[invariant(trail_ok, trail.invariant(*f))]
    loop {
        let base = if confl == cref {0} else {1};
        let mut k: usize = base;
        let clause = &f.clauses[confl];
        #[invariant(kbound, 0 <= @k && @k <= (@clause).len())]
        #[invariant(seen_same_len2, (@seen).len() === @f.num_vars)]
        #[invariant(clause_inv_ok, clause.invariant(*f))]
        #[invariant(out_learnt_len2, (@out_learnt).len() >= 1)]
        #[invariant(out_learnt_ok2, forall<m: Int> 0 <= m && m < (@out_learnt).len() ==>
            @(@out_learnt)[m].idx < @f.num_vars
        )]
        #[invariant(out_learnt_ok_trail2, forall<m: Int> 0 <= m && m < (@out_learnt).len() ==>
            @(@trail.vardata)[@(@out_learnt)[m].idx].0 < (@trail.trail).len()
        )]
        //#[invariant(pathc2, @path_c <= count_true(@seen, 0))]
        #[invariant(pathc2, @path_c <= count_true_range(@seen, 0, (@seen).len()))]
        //#[invariant(pathc2, @path_c <= @f.num_vars)]
        while k < clause.0.len() {
            let lit = clause.0[k];
            let old_seen = Ghost::record(&seen);
            if !seen[lit.idx] {
                let level = trail.vardata[lit.idx].0;
                if level > 0 {
                    seen[lit.idx] = true;
                    proof_assert! {
                        lemma_count_increases_with_true(@seen, @lit.idx);
                        count_true_range(@seen, 0, @lit.idx) === count_true_range(@seen, 0, @lit.idx-1) + 1
                    }
                    /*
                    proof_assert! {
                        lemma_count_increases_with_true(@seen, @lit.idx);
                        count_true(@seen, @lit.idx) === count_true(@seen, @lit.idx+1) + 1
                    }
                    */
                    if level >= decisionlevel {
                        path_c += 1;
                    } else {
                        out_learnt.push(lit);
                    }
                }
            }
            k += 1;
        }
        /*
        let next = {
            #[invariant(iless2, 0 <= @i && @i < (@trail.trail).len())]
            #[invariant(jless2, 0 <= @j && @j <= (@(@trail.trail)[@i]).len())]
            loop { 
                proof_assert!(@j > 0);
                j -= 1;
                if seen[trail.trail[i][j].idx] {
                    break;
                }
                if j == 0 {
                    proof_assert!(@i > 0);
                    i -= 1;
                    j = trail.trail[i].len();
                }
            }
            trail.trail[i][j]
        };
        //proof_assert!(@next.idx < @f.num_vars);
        seen[next.idx] = false;
        // now dlevel = i
        if path_c <= 1 {
            out_learnt[0] = !next;
            break;
        }
        path_c -= 1; // This is moved, TODO: verify that it is correct
        //proof_assert!((@trail.vardata).len() > @next.idx);
        match &trail.vardata[(!next).idx].1 {
            Long(c) => {
                //proof_assert!(@c < (@f.clauses).len());
                confl = *c},
            other => panic!(),
        }
        */
    }   
    /*
    if out_learnt.len() == 1 {
        let lit = out_learnt[0];
        return Conflict::Unit(lit);
    } else {
        // TODO: This section is changed, verify that it is correct
        let mut max_i: usize = 1;
        let mut max_level = trail.vardata[out_learnt[1].idx].0;
        let mut i: usize = 2;
        let out_learnt_len = out_learnt.len();
        #[invariant(iless, 0 <= @i && @i <= (@out_learnt).len())]
        #[invariant(max_i_less, 0 <= @max_i && @max_i < (@out_learnt).len())]
        #[invariant(max_level_less, 0 <= @max_level && @max_level < (@trail.trail).len())]
        while i < out_learnt_len {
            let level = trail.vardata[out_learnt[i].idx].0;
            if level > max_level {
                max_level = level;
                max_i = i;
            }
            i += 1;
        }
        out_learnt.swap(1, max_i);
        return Conflict::Learned(max_level, out_learnt[0], out_learnt);
    }
    */
    return Conflict::Ground;
}