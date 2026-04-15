use creusot_std::prelude::{Clone, *};

use crate::{assignments::*, formula::*, lit::*};

#[derive(Clone)]
pub struct Clause {
    pub deleted: bool,
    pub lbd: u32,
    pub search: usize,
    pub lits: Vec<Lit>, // TODO: unpub
}

impl View for Clause {
    type ViewTy = Seq<Lit>;

    #[logic]
    fn view(self) -> Self::ViewTy {
        self.lits.view() //.push(self.first)//.push(self.second)
    }
}

#[logic]
pub fn vars_in_range_inner(s: Seq<Lit>, n: Int) -> bool {
    pearlite! {
        forall<i: Int> 0 <= i && i < s.len() ==>
            s[i].inv(n)
    }
}

#[logic]
pub fn inv_internal(s: Seq<Lit>, n: Int) -> bool {
    vars_in_range_inner(s, n) && no_duplicate_indexes_inner(s)
}

#[logic]
pub fn equisat_extension_inner(c: Clause, f: (Seq<Clause>, Int)) -> bool {
    pearlite! {
        eventually_sat_complete(f) ==> eventually_sat_complete((f.0.push_back(c), f.1))
    }
}

#[logic]
pub fn no_duplicate_indexes_inner(s: Seq<Lit>) -> bool {
    pearlite! {
        forall<j: Int, k: Int> 0 <= j && j < s.len() &&
                0 <= k && k < j ==> !(s[k].index_logic() == s[j].index_logic())
    }
    /*
    pearlite! {
        forall<j: Int, k: Int> 0 <= j && j < s.len() &&
                k != j ==> !(s[k].index_logic() == s[j].index_logic())
    }
    */
}

impl Clause {
    #[logic]
    pub fn post_unit_inner(self, a: Seq<AssignedState>) -> bool {
        pearlite! {
            exists<i: Int> 0 <= i && i < self@.len() && self@[i].sat_inner(a)
            && forall<j: Int> 0 <= j && j < self@.len() && j != i ==> self@[j].unsat_inner(a)

        }
    }

    #[logic]
    pub fn no_unset_inner(self, a: Seq<AssignedState>) -> bool {
        pearlite! {
            forall<j: Int> 0 <= j && j < self@.len() ==> !self@[j].unset_inner(a)
        }
    }

    #[logic]
    pub fn post_unit(self, a: Assignments) -> bool {
        pearlite! { self.post_unit_inner(a@) }
    }

    #[logic]
    pub fn eq_assn_inner(self, a: Seq<AssignedState>, a2: Seq<AssignedState>) -> bool {
        pearlite! {
            forall<i: Int> 0 <= i && i < self@.len() ==>
                a[self@[i].index_logic()] == a2[self@[i].index_logic()]
        }
    }
}

impl Clause {
    #[logic]
    pub fn equisat_extension(self, f: Formula) -> bool {
        pearlite! { equisat_extension_inner(self, f@) }
    }

    #[logic]
    pub fn same_idx_same_polarity_except(self, other: Clause, exception: Int) -> bool {
        pearlite! {
            forall<i: Int, j: Int> 0 <= i && i < self@.len() && 0 <= j && j < other@.len() ==>
                ((self@[i].index_logic() != exception &&
                self@[i].index_logic() == other@[j].index_logic())) ==>
                self@[i].is_positive_logic() == other@[j].is_positive_logic()
        }
    }

    #[logic]
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

    #[logic]
    pub fn in_formula(self, f: Formula) -> bool {
        pearlite! {
            exists<i: Int> 0 <= i && i < f.clauses@.len() &&
                f.clauses@[i] == self
        }
    }

    #[logic]
    pub fn in_formula_inner(self, f: (Seq<Clause>, Int)) -> bool {
        pearlite! {
            exists<i: Int> 0 <= i && i < (f.0).len() && (f.0)[i] == self
        }
    }

    #[logic]
    fn unit_inner(self, a: Seq<AssignedState>) -> bool {
        pearlite! {
            self.vars_in_range(a.len()) &&
                !self.sat_inner(a) &&
                    exists<i: Int> 0 <= i && i < self@.len() &&
                        self@[i].unset_inner(a) &&
                            (forall<j: Int> 0 <= j && j < self@.len() && j != i ==>
                                !self@[j].unset_inner(a))
        }
    }
    #[logic]
    pub fn unit(self, a: Assignments) -> bool {
        pearlite! { self.unit_inner(a@) }
    }

    #[logic]
    pub fn unsat_inner(self, a: Seq<AssignedState>) -> bool {
        pearlite! {
            forall<i: Int> 0 <= i && i < self@.len() ==>
                self@[i].unsat_inner(a)
        }
    }

    #[logic]
    pub fn unsat(self, a: Assignments) -> bool {
        pearlite! { self.unsat_inner(a@) }
    }

    #[logic]
    pub fn sat_inner(self, a: Seq<AssignedState>) -> bool {
        pearlite! {
            exists<i: Int> 0 <= i && i < self@.len() &&
                self@[i].sat_inner(a)
        }
    }

    #[logic]
    pub fn sat(self, a: Assignments) -> bool {
        pearlite! {
            self.sat_inner(a@)
        }
    }

    #[logic]
    pub fn unknown(self, a: Assignments) -> bool {
        !self.sat(a) && !self.unsat(a)
    }

    #[logic]
    pub fn vars_in_range(self, n: Int) -> bool {
        pearlite! { vars_in_range_inner(self@, n) }
    }

    #[logic]
    pub fn no_duplicate_indexes(self) -> bool {
        pearlite! { no_duplicate_indexes_inner(self@) }
    }

    #[logic]
    pub fn search_idx_in_range(self) -> bool {
        pearlite! { 2 <= self.search@ && self.search@ <= self@.len() }
    }

    #[logic]
    pub fn inv(self, n: Int) -> bool {
        pearlite! { inv_internal(self@, n) }
    }

    #[logic]
    pub fn clause_is_seen(self, seen: Vec<bool>) -> bool {
        pearlite! {
            forall<idx: Int> 0 <= idx && idx < seen@.len() ==>
                (seen@[idx] == idx_in_logic(idx, self@))
        }
    }

    #[logic]
    pub fn equals(self, o: Clause) -> bool {
        pearlite! {
            self@.len() == (o@).len()
            && forall<j: Int> 0 <= j && j < self@.len() ==>
                self@[j] == (o@)[j]
        }
    }
}
