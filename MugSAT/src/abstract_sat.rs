use creusot_contracts::{*, Seq, logic::FSet};

// TODO: I should add sanity lemmas (and eg sat_seq) about the bijection on the `seq`/`set`s

pub struct Lit {
    idx: Int,
    polarity: bool,
}

impl Invariant for Lit {
    #[predicate]
    #[open]
    fn invariant(self) -> bool {
        self.idx >= 0
    }
}

impl Lit {
    #[predicate]
    #[open]
    pub fn sat(self, a: Assignments) -> bool {
        match self.polarity {
            true  =>  a.assignments[self.idx] == AssignedState::True,
            false  => a.assignments[self.idx] == AssignedState::False,
        }
    }

    #[predicate]
    #[open]
    pub fn unsat(self, a: Assignments) -> bool {
        match self.polarity {
            true   => a.assignments[self.idx] == AssignedState::False,
            false  => a.assignments[self.idx] == AssignedState::True,
        }
    }

    #[predicate]
    #[open]
    pub fn unassigned(self, a: Assignments) -> bool {
        a.assignments[self.idx] == AssignedState::Unassigned
    }

    #[predicate]
    #[open]
    pub fn inv(self, n: Int) -> bool {
        self.invariant() && self.idx < n 
    }

    #[logic]
    #[open]
    pub fn opp(self) -> Self {
        Self {
            idx: self.idx,
            polarity: !self.polarity,
        }
    }
}

// "Proof unit tests"
impl Lit {
    #[logic]
    #[requires(self.unassigned(a))]
    #[ensures(!self.sat(a))]
    #[ensures(!self.unsat(a))]
    fn unit_test_unassigned_implies_neither_sat_nor_unsat(self, a: Assignments) {}

    #[logic]
    #[requires(!self.unassigned(a))]
    #[ensures(self.sat(a) || self.unsat(a))]
    fn unit_test_not_unassigned_implies_judged(self, a: Assignments) {}

    #[logic]
    #[requires(self.sat(a))]
    #[ensures(!self.unassigned(a))]
    #[ensures(!self.unsat(a))]
    fn unit_test_sat_implies_neither_unsat_nor_unassigned(self, a: Assignments) {}

    #[logic]
    #[requires(self.unsat(a))]
    #[ensures(!self.unassigned(a))]
    #[ensures(!self.sat(a))]
    fn unit_test_sat_implies_neither_sat_nor_unassigned(self, a: Assignments) {}

    #[logic]
    #[ensures(self.opp().opp() == self)]
    #[ensures(self.invariant() ==> self.opp().invariant())]
    #[ensures(self.opp().invariant() ==> self.invariant())]
    #[ensures(self.opp().idx == self.idx && self.opp().polarity != self.polarity)]
    fn unit_test_opp(self) {}
}

pub struct Clause {
    clause_seq: Seq<Lit>,
    clause_set: FSet<Lit>,
}

impl Invariant for Clause {
    #[predicate]
    #[open]
    fn invariant(self) -> bool {
        pearlite! {
            self.no_duplicate_indexes() // Is this actually needed for anything?
            && self.clause_seq.len() == self.clause_set.len() // This isn't really needed for anything is it? Just remove it?
            && (forall<i: _> 0 <= i && i < self.clause_seq.len() ==> self.clause_set.contains(self.clause_seq[i]))
            && (forall<l: _> self.clause_set.contains(l) ==> self.clause_seq.contains(l)) //(exists<i: Int> 0 <= i && i < self.clause_seq.len() && self.clause_seq[i] == l))
        }
    }
}

impl Clause {
    #[predicate]
    #[open]
    pub fn sat(self, a: Assignments) -> bool {
        pearlite! {
            exists<l: _> self.clause_set.contains(l) && l.sat(a)
        }
    }

    #[predicate]
    #[open]
    pub fn sat_seq(self, a: Assignments) -> bool {
        pearlite! {
            exists<l: _> self.clause_seq.contains(l) && l.sat(a)
        }
    }

    #[predicate]
    #[open]
    pub fn unsat(self, a: Assignments) -> bool {
        pearlite! {
            forall<l: _> self.clause_set.contains(l) ==> l.unsat(a)
        }
    }

    #[predicate]
    #[open]
    pub fn unsat_seq(self, a: Assignments) -> bool {
        pearlite! {
            forall<l: _> self.clause_seq.contains(l) ==> l.unsat(a)
        }
    }

    #[predicate]
    #[open]
    pub fn is_judged(self, a: Assignments) -> bool {
        self.sat(a) || self.unsat(a)
    }

    #[predicate]
    #[open]
    pub fn is_covered(self, a: Assignments) -> bool {
        pearlite! {
            forall<l: _> self.clause_set.contains(l) ==> !l.unassigned(a)
        }
    }
    
    #[predicate]
    #[open]
    pub fn is_covered_seq(self, a: Assignments) -> bool {
        pearlite! {
            forall<i: Int> 0 <= i && i < self.clause_seq.len() ==> !self.clause_seq[i].unassigned(a)
        }
    }

    #[logic]
    #[open]
    pub fn len(self) -> Int {
        self.clause_set.len()
    }

    #[predicate]
    #[open]
    pub fn no_duplicate_indexes(self) -> bool {
        pearlite! {
            forall<j: Int, k: Int> 0 <= j && j < self.len() &&
                    0 <= k && k < self.len() && k != j ==> self.clause_seq[k].idx != self.clause_seq[j].idx
        }
    }

    #[predicate]
    #[open]
    pub fn vars_in_range(self, n: Int) -> bool {
        pearlite! {
            forall<i: Int> 0 <= i && i < self.len() ==> self.clause_seq[i].inv(n)
        }
    }

    #[predicate]
    #[open]
    pub fn vars_in_range_set(self, n: Int) -> bool {
        pearlite! {
            forall<l: _> self.clause_set.contains(l) ==> l.inv(n)
        }
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

    // TODO: This really should have the set version of vars in range, no?
    #[predicate]
    #[open]
    pub fn inv(self, n: Int) -> bool {
        self.invariant() && self.vars_in_range_set(n) // && self.vars_in_range_set(n)
    }

    /*
    #[predicate]
    #[open]
    pub fn resolvent_of(self, c: Clause, c2: Clause, k: Int, m: Int) -> bool {
        pearlite! {
            /*
            (forall<i: Int> 0 <= i && i < c @.len() && i != m ==>  c   @[i].lit_in(self)) &&
            (forall<i: Int> 0 <= i && i < c2@.len() && i != k ==>  c2  @[i].lit_in(self)) &&
            (forall<i: Int> 0 <= i && i < self@.len()         ==> (self@[i].lit_in(c)
                                                                || self@[i].lit_in(c2))) &&
            !c@[m].lit_in(self) && !c2@[k].lit_in(self) &&
            c2@[k].is_opp(c@[m])
            */
        }
    }
    */

    // TODO: Is this better with indexes or with the lit
    #[predicate]
    #[open]
    pub fn resolvent_of(self, c1: Clause, c2: Clause, o: Lit) -> bool {
        pearlite! {
               (forall<l: _> c1.clause_set.contains(l) && l != o        ==> self.clause_set.contains(l)) 
            && (forall<l: _> c2.clause_set.contains(l) && l != o.opp()  ==> self.clause_set.contains(l))
            // TODO: This is equivalent to stating that the len == c1.len() + c2.len() - 2, is one better than the other?
            && (forall<l: _> self.clause_set.contains(l) ==> (c1.clause_set.contains(l) || c2.clause_set.contains(l)))
            // && self.clause_set.len() == c1.clause_set.len() + c2.clause_set.len() - 2
            && !self.clause_set.contains(o)
            && !self.clause_set.contains(o.opp())
            && c1.clause_set.contains(o) 
            && c2.clause_set.contains(o.opp())
        }
    }
}

// "proof unit tests"
impl Clause {
    #[logic]
    #[requires(self.invariant())] // TODO: this should be removable
    #[requires(self.len() == 0)]
    #[ensures(self.unsat(a))]
    fn unit_test_empty_clause_is_unsat(self, a: Assignments) {}

    #[logic]
    #[requires(self.invariant())] // TODO: this should be removable
    #[ensures(self.len() == self.clause_seq.len())]
    #[ensures(self.len() == self.clause_set.len())]
    #[ensures(self.clause_seq.len() == self.clause_set.len())]
    fn unit_test_len_equalities(self) {}

    #[logic]
    #[requires(self.invariant())] // TODO: this should be removable
    #[ensures(
        forall<j: Int, k: Int> 0 <= j && j < self.len() &&
        0 <= k && k < self.len() && k != j ==> self.clause_seq[k] != self.clause_seq[j]
    )]
    fn unit_test_no_duplicates_implies(self) {}

    #[logic]
    #[requires(self.invariant())] // TODO: this should be removable
    #[requires(self.sat(a))]
    #[ensures(self.sat_seq(a))]
    #[ensures(!self.unsat_seq(a))]
    #[ensures(!self.unsat(a))]
    fn unit_test_sat(self, a: Assignments) {}

    #[logic]
    #[requires(self.invariant())] // TODO: this should be removable
    #[requires(self.unsat(a))]
    #[ensures(self.unsat_seq(a))]
    #[ensures(!self.sat_seq(a))]
    #[ensures(!self.sat(a))]
    fn unit_test_unsat(self, a: Assignments) {}

    #[logic]
    #[requires(self.inv(a.len()))] 
    #[requires(self.is_covered(a))]
    #[ensures(self.is_judged(a))]
    fn unit_test_covered_is_judged(self, a: Assignments) {}

    #[logic]
    #[requires(self.inv(a.len()))] 
    #[ensures(self.is_covered(a) ==> self.is_covered_seq(a))]
    #[ensures(self.is_covered_seq(a) ==> self.is_covered(a))]
    fn unit_test_covered_bijection(self, a: Assignments) {}

    #[logic]
    #[requires(self.inv(n) && c1.inv(n) && c2.inv(n))]
    #[requires(self.resolvent_of(c1, c2, o))]
    #[ensures(c1.clause_set.contains(o))]
    #[ensures(c2.clause_set.contains(o.opp()))]
    #[ensures(!self.clause_set.contains(o))]
    #[ensures(!self.clause_set.contains(o.opp()))]
    #[ensures(c1.len() > 0)]
    #[ensures(c2.len() > 0)]
    //#[ensures(self.inv(n))]
    #[ensures(self.vars_in_range_set(n))]
    // TODO: Figure out why this aint proving
    // #[ensures(self.clause_set.len() <= c1.clause_set.len() + c2.clause_set.len())]
    //#[ensures(forall<l: _> self.clause_set.contains(l) ==> (c1.clause_set.contains(l) || c2.clause_set.contains(l)))]
    fn unit_test_resolvent(self, c1: Clause, c2: Clause, o: Lit, n: Int) {
        /*
        proof_assert!(forall<l: _> c1.clause_set.contains(l) && l != o        ==> self.clause_set.contains(l));
        proof_assert!(forall<l: _> c2.clause_set.contains(l) && l != o.opp()  ==> self.clause_set.contains(l));
        proof_assert!(self.clause_set.len() == c1.clause_set.len() + c2.clause_set.len() - 2);
        */

    }

    #[logic]
    #[requires(self.inv(f.num_vars) && f.inv())]
    #[requires(self.resolvent_of(c1, c2, o))]
    #[requires(f.formula_seq.contains(c1) && f.formula_seq.contains(c2))]
    #[ensures(c1.inv(f.num_vars))]
    #[ensures(c2.inv(f.num_vars))]
    #[requires(self.inv(f.num_vars))]
    //#[ensures(f.implies(self))]
    fn unit_test_resolvent_implied(self, c1: Clause, c2: Clause, o: Lit, f: Formula) {}
}



pub struct Formula {
    formula_seq: Seq<Clause>,
    formula_set: FSet<Clause>,
    num_vars: Int,
}

impl Formula {
    #[open]
    #[logic]
    fn insert(self, clause: Clause) -> Formula {
        Formula { formula_seq: self.formula_seq.push_back(clause), formula_set: self.formula_set.insert(clause), num_vars: self.num_vars }
    }
}


impl Formula {
    #[logic]
    #[open]
    #[ensures(self.insert(clause).num_vars == self.num_vars)]
    //#[ensures((self.invariant() && clause.inv(self.num_vars)) ==> self.insert(clause).invariant())]
    #[requires(self.invariant())]
    #[requires(clause.inv(self.num_vars))]
    #[requires(o == self.insert(clause))]
    #[ensures(o.inv())]
    #[ensures(o.inv_set())]
    #[ensures((forall<i: _> 0 <= i && i < o.formula_seq.len() ==> o.formula_set.contains(o.formula_seq[i])))]
    #[ensures((forall<c: _> o.formula_set.contains(c) ==> exists<i: Int> 0 <= i && i < o.formula_seq.len() && o.formula_seq[i] == c))]
    fn unit_test_insert(self, clause: Clause, o: Self) {}
}

impl Formula {
    #[predicate]
    #[open]
    pub fn sat(self, a: Assignments) -> bool {
        pearlite! {
            forall<c: _> self.formula_set.contains(c) ==> c.sat(a)
        }
    }

    #[predicate]
    #[open]
    pub fn unsat(self, a: Assignments) -> bool {
        pearlite! {
            exists<c: _> self.formula_set.contains(c) && c.unsat(a)
        }
    }

    #[predicate]
    #[open]
    pub fn eventually_sat_complete(self) -> bool {
        pearlite! {
            exists<a: Assignments> a.len() == self.num_vars && a.complete() && self.sat(a)
        }
    }

    // TODO: Swap to equisat extension?
    #[predicate]
    #[open]
    pub(crate) fn implies(self, clause: Clause) -> bool {
        pearlite! {
            self.eventually_sat_complete() ==> self.insert(clause).eventually_sat_complete()
        }
    }

    #[predicate]
    #[open]
    pub fn equisat(self, o: Formula) -> bool {
        self.eventually_sat_complete() == o.eventually_sat_complete()
    }

    // TODO: Add the len() > 0 invariant? Is there anything which relies on it?
    #[predicate]
    #[open]
    pub fn inv(self) -> bool {
        pearlite! {
            forall<i: Int> 0 <= i && i < self.formula_seq.len() ==>
                self.formula_seq[i].inv(self.num_vars) /* && self.formula_seq[i].len() > 0 */
        }
    }

    #[predicate]
    #[open]
    pub fn inv_set(self) -> bool {
        pearlite! {
            forall<c: _> self.formula_set.contains(c) ==>
                c.inv(self.num_vars) /* && c.len() > 0 */
        }
    }
}

impl Invariant for Formula {
    #[predicate]
    #[open]
    fn invariant(self) -> bool {
        pearlite! {
            self.inv()
            && self.inv_set()
            && (forall<i: _> 0 <= i && i < self.formula_seq.len() ==> self.formula_set.contains(self.formula_seq[i]))
            && (forall<c: _> self.formula_set.contains(c) ==> exists<i: Int> 0 <= i && i < self.formula_seq.len() && self.formula_seq[i] == c)
        }
    }
}

// "Proof unit tests"
impl Formula {
    #[logic]
    #[requires(self.sat(a))]
    #[ensures(!self.unsat(a))]
    #[open]
    fn sat_excludes(self, a: Assignments) {}

    #[logic]
    #[requires(self.unsat(a))]
    #[ensures(!self.sat(a))]
    #[open]
    fn unsat_excludes(self, a: Assignments) {}
}



pub struct FormulaDouble {
    formula_initial: Formula,
    formula_current: Formula,
}

impl Invariant for FormulaDouble {
    #[predicate]
    #[open]
    fn invariant(self) -> bool {
        true
    }
}

pub enum AssignedState {
    False,
    True,
    Unassigned,
}

impl AssignedState {
    #[predicate]
    #[open]
    pub fn is_set(self) -> bool {
        match self {
            Self::Unassigned => false,
            _ => true,
        }
    }
        // !self.is_unset()

    #[predicate]
    #[open]
    pub fn is_unset(self) -> bool {
        match self {
            Self::Unassigned => true,
            _ => false,
        }
    }
}

struct Assignments {
    // TODO: Swap Seq with a map?
    assignments: Seq<AssignedState>
}

impl Assignments {
    #[logic]
    #[open]
    pub fn len(self) -> Int {
        self.assignments.len()
    }

    #[predicate]
    #[open]
    pub fn complete(self) -> bool {
        pearlite! {
            forall<i: Int> 0 <= i && i < self.len() ==> self.assignments[i].is_set()
        }
    }
}

// "proof unit tests"
impl Assignments {
    #[logic]
    #[requires(self.complete())]
    #[requires(f.invariant() && self.len() == f.num_vars && self.len() == 2)]
    #[ensures(!f.sat(self) ==> f.unsat(self))]
    #[ensures(!f.unsat(self) ==> f.sat(self))]
    #[ensures(f.sat(self) || f.unsat(self))]
    fn complete_assignments_are_judging(self, f: Formula) {
        // TODO: Remove body. We don't need them to prove anything just useful extra assertions
        proof_assert!(forall<i: Int> 0 <= i && i < self.len() ==> self.assignments[i] != AssignedState::Unassigned);
        proof_assert!(forall<i: Int> 0 <= i && i < f.num_vars ==> self.assignments[i] != AssignedState::Unassigned);
        proof_assert!(forall<c: _> f.formula_set.contains(c) ==> c.is_judged(self));
        proof_assert!(forall<c: _> f.formula_seq.contains(c) ==> c.is_judged(self));
        proof_assert!(forall<c: _> f.formula_seq.contains(c) ==> c.is_covered(self));
        proof_assert!(forall<c: _> f.formula_set.contains(c) ==> c.is_covered_seq(self));
        proof_assert!(forall<c: _> f.formula_set.contains(c) ==> forall<l: _> c.clause_set.contains(l) ==> l.inv(self.len()));
        proof_assert!(forall<c: _> f.formula_set.contains(c) ==> forall<l: _> c.clause_seq.contains(l) ==> l.inv(self.len()));
        proof_assert!(forall<c: _> f.formula_set.contains(c) ==> forall<l: _> c.clause_seq.contains(l) ==> self.assignments.get(l.idx) != None);
    }
}

/*
#[predicate]
#[open]
#[cfg_attr(feature = "trust_formula_logic", trusted)]
#[ensures(result == self.inv_mirror())] // Removing this makes a bunch of seemingly unrelated things fail
pub fn inv(self) -> bool {
    pearlite! { formula_invariant(self@) }
}

#[predicate]
#[open]
pub fn inv_mirror(self) -> bool {
    pearlite! {
        (forall<i: Int> 0 <= i && i < self.clauses@.len() ==>
            self.clauses@[i].inv(self.num_vars@))
        &&
        (forall<i: Int> 0 <= i && i < self.clauses@.len() ==>
            self.clauses@[i]@.len() >= 1)

    }
}
    #[predicate]
#[open]
pub fn formula_invariant(f: FormulaModel) -> bool {
    pearlite! {
        forall<i: Int> 0 <= i && i < f.clauses.len() ==>
            (f.clauses[i].inv(f.num_vars) && f.clauses[i]@.len() > 0)
    }
}
*/