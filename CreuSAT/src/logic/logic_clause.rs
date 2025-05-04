
use creusot_contracts::std::*;
use creusot_contracts::*;

use crate::{assignments::*, clause::*, formula::*, lit::*};

#[cfg(creusot)]
use crate::logic::{logic_assignments::complete_inner, logic_formula::*, logic_lit::idx_in_logic};

#[cfg(creusot)]
impl View for Clause {
    type ViewTy = Seq<Lit>;

    #[logic]
    #[open]
    fn view(self) -> Self::ViewTy {
        self.lits.view() //.push(self.first)//.push(self.second)
    }
}

#[predicate]
#[open]
pub fn vars_in_range_inner(s: Seq<Lit>, n: Int) -> bool {
    pearlite! {
        forall<i: Int> 0 <= i && i < s.len() ==>
            s[i].inv(n)
    }
}

#[predicate]
#[open]
pub fn inv_internal(s: Seq<Lit>, n: Int) -> bool {
    vars_in_range_inner(s, n) && no_duplicate_indexes_inner(s)
}

#[predicate]
#[open]
pub fn equisat_extension_inner(c: Clause, f: FormulaModel) -> bool {
    pearlite! {
        eventually_sat_complete(f) ==> eventually_sat_complete(FormulaModel { clauses: f.clauses.push(c), num_vars: f.num_vars })
    }
}

#[predicate]
#[open]
pub fn no_duplicate_indexes_inner(s: Seq<Lit>) -> bool {
    pearlite! {
        forall<j: Int, k: Int> 0 <= j && j < s.len() &&
                0 <= k && k < s.len() && k != j ==> s[k].index_logic() != s[j].index_logic()
    }
    /*
    // The previous one
    pearlite! {
        forall<j: Int, k: Int> 0 <= j && j < s.len() &&
                0 <= k && k < j ==> !(s[k].index_logic() == s[j].index_logic())
    }
    */
    /*
    pearlite! {
        forall<j: Int, k: Int> 0 <= j && j < s.len() &&
                k != j ==> !(s[k].index_logic() == s[j].index_logic())
    }
    */
}

impl Clause {
    #[predicate]
    #[open]
    pub fn post_unit_inner(self, a: Seq<AssignedState>) -> bool {
        pearlite! {
            exists<i: Int> 0 <= i && i < self@.len() && self@[i].sat_inner(a)
            && forall<j: Int> 0 <= j && j < self@.len() && j != i ==> self@[j].unsat_inner(a)

        }
    }

    #[predicate]
    #[open]
    pub fn no_unset_inner(self, a: Seq<AssignedState>) -> bool {
        pearlite! {
            forall<j: Int> 0 <= j && j < self@.len() ==> !self@[j].unset_inner(a)
        }
    }

    #[predicate]
    #[open]
    pub fn post_unit(self, a: Assignments) -> bool {
        pearlite! { self.post_unit_inner(a@) }
    }

    #[predicate]
    #[open]
    pub fn eq_assn_inner(self, a: Seq<AssignedState>, a2: Seq<AssignedState>) -> bool {
        pearlite! {
            forall<i: Int> 0 <= i && i < self@.len() ==>
                a[self@[i].index_logic()] == a2[self@[i].index_logic()]
        }
    }
}

impl Clause {
    #[predicate]
    #[open]
    pub fn equisat_extension(self, f: Formula) -> bool {
        pearlite! { equisat_extension_inner(self, f@) }
    }

    #[predicate]
    #[open]
    pub fn same_idx_same_polarity_except(self, other: Clause, exception: Int) -> bool {
        pearlite! {
            forall<i: Int, j: Int> 0 <= i && i < self@.len() && 0 <= j && j < other@.len() ==>
                ((self@[i].index_logic() != exception &&
                self@[i].index_logic() == other@[j].index_logic())) ==>
                self@[i].is_positive_logic() == other@[j].is_positive_logic()
        }
    }

    #[predicate]
    #[open]
    pub fn resolvent_of(self, c: Clause, c2: Clause, k: Int, m: Int) -> bool {
        pearlite! {
            (forall<i: Int> 0 <= i && i < c @.len() && i != m ==>  c   @[i].lit_in(self)) &&
            (forall<i: Int> 0 <= i && i < c2@.len() && i != k ==>  c2  @[i].lit_in(self)) &&
            (forall<i: Int> 0 <= i && i < self@.len()         ==> (self@[i].lit_in(c)
                                                                || self@[i].lit_in(c2))) &&
            !c@[m].lit_in(self) && !c2@[k].lit_in(self) &&
            c2@[k].is_opp(c@[m])
        }
    }

    #[predicate]
    #[open]
    pub fn in_formula(self, f: Formula) -> bool {
        pearlite! {
            exists<i: Int> 0 <= i && i < f.clauses@.len() &&
                f.clauses@[i] == self
        }
    }

    #[predicate]
    #[open]
    pub fn in_formula_inner(self, f: FormulaModel) -> bool {
        pearlite! {
            exists<i: Int> 0 <= i && i < f.clauses.len() && f.clauses[i] == self
        }
    }

    #[predicate]
    #[open]
    pub fn unit_inner(self, a: Seq<AssignedState>) -> bool {
        pearlite! {
            self.vars_in_range(a.len()) &&
                !self.sat_inner(a) &&
                    exists<i: Int> 0 <= i && i < self@.len() &&
                        self@[i].unset_inner(a) &&
                            (forall<j: Int> 0 <= j && j < self@.len() && j != i ==>
                                !self@[j].unset_inner(a))
        }
    }

    #[predicate]
    #[open] //#[open(self)]
    pub fn unit(self, a: Assignments) -> bool {
        pearlite! { self.unit_inner(a@) }
    }

    #[predicate]
    #[open]
    pub fn unsat_inner(self, a: Seq<AssignedState>) -> bool {
        pearlite! {
            forall<i: Int> 0 <= i && i < self@.len() ==>
                self@[i].unsat_inner(a)
        }
    }

    #[predicate]
    #[open]
    pub fn unsat(self, a: Assignments) -> bool {
        pearlite! { self.unsat_inner(a@) }
    }

    #[predicate]
    #[open]
    pub fn sat_inner(self, a: Seq<AssignedState>) -> bool {
        pearlite! {
            exists<i: Int> 0 <= i && i < self@.len() &&
                self@[i].sat_inner(a)
        }
    }

    #[predicate]
    #[open]
    pub fn sat(self, a: Assignments) -> bool {
        pearlite! {
            self.sat_inner(a@)
        }
    }

    #[predicate]
    #[open]
    pub fn unknown(self, a: Assignments) -> bool {
        !self.sat(a) && !self.unsat(a)
    }

    #[predicate]
    #[open]
    pub fn vars_in_range(self, n: Int) -> bool {
        pearlite! { vars_in_range_inner(self@, n) }
    }

    #[predicate]
    #[open]
    pub fn no_duplicate_indexes(self) -> bool {
        pearlite! { no_duplicate_indexes_inner(self@) }
    }

    #[predicate]
    #[open]
    pub fn search_idx_in_range(self) -> bool {
        pearlite! { 2 <= self.search@ && self.search@ <= self@.len() }
    }

    #[predicate]
    #[open]
    pub fn inv(self, n: Int) -> bool {
        pearlite! { invariant_internal(self@, n) }
    }

    #[predicate]
    #[open]
    pub fn clause_is_seen(self, seen: Vec<bool>) -> bool {
        pearlite! {
            forall<idx: Int> 0 <= idx && idx < seen@.len() ==>
                (seen@[idx] == idx_in_logic(idx, self@))
        }
    }

    #[predicate]
    #[open]
    pub fn equals(self, o: Clause) -> bool {
        pearlite! {
            self@.len() == o@.len()
            && forall<j: Int> 0 <= j && j < self@.len() ==>
                self@[j] == o@[j]
        }
    }
}

#[cfg_attr(feature = "trust_logic_logic", trusted)]
#[logic]
#[open(self)]
#[requires(formula_invariant(f))]
#[requires(equisat_extension_inner(c, f))]
#[requires(c@.permutation_of(c2@))]
#[ensures(equisat_extension_inner(c2, f))]
pub fn lemma_permuted_clause_maintains_equisat(f: FormulaModel, c: Clause, c2: Clause) {}

#[logic]
#[requires(no_duplicate_indexes_inner(c1@))]
#[requires(exists<i: _, j: _ > c2@.exchange(c1@, j, i))]
#[ensures(c1@.permutation_of(c2@))]
#[ensures(c2@.permutation_of(c1@))]
#[ensures(no_duplicate_indexes_inner(c2@))]
#[open]
pub fn dup_stable_on_permut(c1: Clause, c2: Clause) {}
