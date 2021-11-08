#![feature(type_ascription)]

extern crate creusot_contracts;

use creusot_contracts::std::*;
use creusot_contracts::*;

pub struct Ghost<T>(*mut T)
where
    T: ?Sized;

impl<T> Model for Ghost<T> {
    type ModelTy = T;
    #[logic]
    #[trusted]
    fn model(self) -> Self::ModelTy {
        panic!()
    }
}

impl<T> Ghost<T> {
    #[trusted]
    #[ensures(@result === *a)]
    fn record(a: &T) -> Ghost<T> {
        panic!()
    }
}

#[derive(Clone, Copy)]
struct Lit {
    idx: usize,
    polarity: bool,
}
struct Clause(Vec<Lit>);
struct Assignments(Vec<AssignedState>);

impl Model for Assignments {
    type ModelTy = Seq<AssignedState>;

    #[logic]
    fn model(self) -> Self::ModelTy {
        self.0.model()
    }
}

impl Model for Clause {
    type ModelTy = Seq<Lit>;

    #[logic]
    fn model(self) -> Self::ModelTy {
        self.0.model()
    }
}

pub struct Formula {
    clauses: Vec<Clause>,
    num_vars: usize,
}

#[derive(Copy, Clone, Eq)]
pub enum SatState {
    Unknown,
    Sat,
    Unsat,
}

#[derive(Copy, Eq)]
pub enum AssignedState {
    Unset,
    Positive,
    Negative,
}

impl PartialEq for SatState {
    #[trusted]
    fn eq(&self, other: &Self) -> bool {
        return match (self, other) {
            (SatState::Unknown, SatState::Unknown) => true,
            (SatState::Sat, SatState::Sat) => true,
            (SatState::Unsat, SatState::Unsat) => true,
            _ => false,
        };
    }
}

impl PartialEq for AssignedState {
    #[trusted]
    fn eq(&self, other: &Self) -> bool {
        return match (self, other) {
            (AssignedState::Unset, AssignedState::Unset) => true,
            (AssignedState::Positive, AssignedState::Positive) => true,
            (AssignedState::Negative, AssignedState::Negative) => true,
            _ => false,
        };
    }
}

fn main() {}

#[logic]
#[variant(a.len())]
fn unassigned_count(a: Seq<AssignedState>) -> Int {
    if a.len() == 0 {
        0
    } else if pearlite! { a[0] === AssignedState::Unset } {
        1 + unassigned_count(a.tail())
    } else {
        unassigned_count(a.tail())
    }
}

#[predicate]
fn assignments_equality(a: Assignments, a2: Assignments) -> bool {
    pearlite! {
        (@a).len() === (@a2).len() &&
        forall<i: Int> 0 <= i && i < (@a).len() ==> (@a)[i] === (@a2)[i]
    }
}

#[predicate]
fn vars_in_range(n: Int, c: Clause) -> bool {
    pearlite! {
        forall<i: Int> 0 <= i && i < (@c).len() ==>
            (0 <= @((@c)[i]).idx && @((@c)[i]).idx < n)
    }
}

#[predicate]
fn compatible_inner(a: Seq<AssignedState>, a2: Seq<AssignedState>) -> bool {
    pearlite! {
        a.len() === a2.len() &&
        forall<i: Int> 0 <= i && i < a.len() ==>
        (a[i] === AssignedState::Unset) || a[i] === a2[i]
    }
}

#[predicate]
fn complete_inner(a: Seq<AssignedState>) -> bool {
    pearlite! {
        forall<i: Int> 0 <= i && i < a.len() ==> !(a[i] === AssignedState::Unset)
    }
}

#[predicate]
fn compatible_complete_inner(a: Seq<AssignedState>, a2: Seq<AssignedState>) -> bool {
    pearlite! {
        compatible_inner(a, a2) && complete_inner(a2)
    }
}

#[predicate]
fn not_sat_clause_inner(a: Seq<AssignedState>, c: Clause) -> bool {
    pearlite! {
        forall<i: Int> 0 <= i && i < (@c).len() ==>
            match a[@(@c)[i].idx] {
                AssignedState::Positive => !(@c)[i].polarity,
                AssignedState::Negative => (@c)[i].polarity,
                AssignedState::Unset => false,
            }
    }
}

impl Clause {
    #[predicate]
    fn unsat(self, a: Assignments) -> bool {
        pearlite! {
            forall<i: Int> 0 <= i && i < (@self).len() ==>
                match (@a)[@(@self)[i].idx] {
                    AssignedState::Positive => !(@self)[i].polarity,
                    AssignedState::Negative => (@self)[i].polarity,
                    AssignedState::Unset => false,
                }
        }
    }

    #[predicate]
    fn sat(self, a: Assignments) -> bool {
        pearlite! {
            exists<i: Int> 0 <= i && i < (@self).len() &&
                match (@a)[@(@self)[i].idx] {
                    AssignedState::Positive => (@self)[i].polarity,
                    AssignedState::Negative => !(@self)[i].polarity,
                    AssignedState::Unset => false
                }
        }
    }

    #[predicate]
    fn unknown(self, a: Assignments, c: Clause) -> bool {
        !self.sat(a) && !self.unsat(a)
    }
}

#[predicate]
fn eventually_unsat_formula_inner(a: Seq<AssignedState>, f: Formula) -> bool {
    pearlite! {
        forall<a2: Seq<AssignedState>> compatible_complete_inner(a, a2) ==> not_sat_formula_inner(a2, f)
    }
}

#[predicate]
fn not_sat_formula_inner(a: Seq<AssignedState>, f: Formula) -> bool {
    pearlite! {
        exists<i: Int> 0 <= i && i < (@(f.clauses)).len() &&
        not_sat_clause_inner(a, (@(f.clauses))[i])
    }
}

#[ensures(result === (@f.clauses)[@idx].sat(*a))]
#[requires(f.invariant())]
#[requires(a.invariant(*f))]
#[requires(@idx < (@f.clauses).len())]
fn is_clause_sat(f: &Formula, idx: usize, a: &Assignments) -> bool {
    let clause = &f.clauses[idx];
    let mut i = 0;
    #[invariant(previous, forall<j: Int> 0 <= j && j < @i ==>
        match (@a)[@(@clause)[j].idx] {
            AssignedState::Positive => !(@clause)[j].polarity,
            AssignedState::Negative => (@clause)[j].polarity,
            AssignedState::Unset => true,
        }
    )]
    while i < clause.0.len() {
        let lit = clause.0[i];
        match a.0[lit.idx]{
           AssignedState::Positive => {
                if lit.polarity {
                    return true
                }
            },
            AssignedState::Negative => {
                if !lit.polarity {
                    return true
                }
            },
            AssignedState::Unset => {
            }
        }
        i += 1;
    }
    return false;
}

#[ensures(result === (@f.clauses)[@idx].unsat(*a))]
#[requires(f.invariant())]
#[requires(a.invariant(*f))]
#[requires(@idx < (@f.clauses).len())]
fn is_clause_unsat(f: &Formula, idx: usize, a: &Assignments) -> bool {
    let clause = &f.clauses[idx];
    let mut i = 0;
    #[invariant(loop_invariant, 0 <= @i && @i <= (@clause).len())]
    #[invariant(previous, forall<j: Int> 0 <= j && j < @i ==>
        match (@a)[@(@clause)[j].idx] {
            AssignedState::Positive => !(@clause)[j].polarity,
            AssignedState::Negative => (@clause)[j].polarity,
            AssignedState::Unset => false,
        }
    )]
    while i < clause.0.len() {
        let lit = clause.0[i];
        match a.0[lit.idx]{
           AssignedState::Positive => {
                if lit.polarity {
                    return false
                }
            },
            AssignedState::Negative => {
                if !lit.polarity {
                    return false
                }
            },
            AssignedState::Unset => {
                return false;
            }
        }
        i += 1;
    }
    return true;
}

impl Formula {
    #[predicate]
    fn invariant(self) -> bool {
        pearlite! {
            (forall<i: Int> 0 <= i && i < (@(self.clauses)).len() ==>
            vars_in_range(@(self.num_vars), ((@(self.clauses))[i])))
        }
    }

    #[requires(self.invariant())]
    #[requires(a.invariant(*self))]
    #[ensures(result === self.unsat(*a))]
    fn is_unsat(&self, a: &Assignments) -> bool {
        let mut i = 0;
        #[invariant(prev,
            forall<k: Int> 0 <= k && k < @i ==>
            !(@self.clauses)[k].unsat(*a))]
        #[invariant(loop_invariant, 0 <= @i && @i <= (@self.clauses).len())]
        while i < self.clauses.len() {
            if is_clause_unsat(self, i, a) {
                return true;
            }
            i += 1;
        }
        return false;
    }

    #[requires(self.invariant())]
    #[requires(a.invariant(*self))]
    #[ensures(result === self.sat(*a))]
    fn is_sat(&self, a: &Assignments) -> bool {
        let mut i = 0;
        #[invariant(prev,
            forall<k: Int> 0 <= k && k < @i ==>
            (@self.clauses)[k].sat(*a))]
        #[invariant(loop_invariant, 0 <= @i && @i <= (@self.clauses).len())]
        while i < self.clauses.len() {
            if !is_clause_sat(self, i, a) {
                return false;
            }
            i += 1
        }
        return true;
    }

    #[requires(self.invariant())]
    #[requires(a.invariant(*self))]
    #[ensures((result === SatState::Sat) === self.sat(*a))]
    #[ensures((result === SatState::Unsat) === self.unsat(*a))]
    #[ensures((result === SatState::Unknown) ==> !a.complete())]
    fn eval(&self, a: &Assignments) -> SatState {
        if self.is_sat(a) {
            return SatState::Sat;
        } else if self.is_unsat(a) {
            return SatState::Unsat;
        } else {
            return SatState::Unknown;
        }
    }

    #[predicate]
    fn eventually_sat(self, a: Assignments) -> bool {
        pearlite! {
            exists<a2 : Assignments> a.compatible(a2) && self.sat(a2)
        }
    }

    #[predicate]
    fn eventually_unsat(self, a: Assignments) -> bool {
        pearlite! { eventually_unsat_formula_inner(@a, self) }
    }

    #[predicate]
    fn sat(self, a: Assignments) -> bool {
        pearlite! {
            forall<i: Int> 0 <= i && i < (@(self.clauses)).len() ==>
            (@(self.clauses))[i].sat(a)
        }
    }

    #[predicate]
    fn unsat(self, a: Assignments) -> bool {
        pearlite! {
            exists<i: Int> 0 <= i && i < (@(self.clauses)).len() &&
            (@(self.clauses))[i].unsat(a)
        }
    }
}

impl Assignments {
    #[predicate]
    fn invariant(self, f: Formula) -> bool {
        pearlite! {
            @f.num_vars === (@self).len()
        }
    }

    #[predicate]
    fn compatible_complete(self, a2: Assignments) -> bool {
        self.compatible(a2) && a2.complete()
    }

    #[predicate]
    fn complete(self) -> bool {
        pearlite! {
            forall<i: Int> 0 <= i && i < (@self).len() ==> !((@self)[i] === AssignedState::Unset)
        }
    }

    #[trusted]
    #[ensures(
        forall<i: Int> 0 <= i && i < (@v).len() ==>
        (@v)[i] === (@result)[i]
    )]
    #[ensures((@v).len() === (@result).len())]
    #[ensures(*v === result)]
    fn clone_assignment_vector(&self, v: &Vec<AssignedState>) -> Vec<AssignedState> {
        let mut out = Vec::new();
        let mut i = 0;
        #[invariant(loop_invariant, 0 <= @i && @i <= (@v).len())]
        #[invariant(equality, forall<j: Int> 0 <= j && j < @i ==> (@out)[j] === (@v)[j])]
        while i < v.len() {
            let curr = v[i];
            out.push(curr.clone());
            i += 1;
        }
        return out;
    }
    #[trusted]
    #[ensures(
        forall<i: Int> 0 <= i && i < (@self).len() ==>
        (@self)[i] === (@result)[i]
    )]
    #[ensures((@self).len() === (@result).len())]
    #[ensures(*self === result)]
    fn clone(&self) -> Self {
        Assignments(self.clone_assignment_vector(&self.0))
    }

    #[requires(f.invariant())]
    #[ensures(result.invariant(*f))]
    fn new(f: &Formula) -> Self {
        let mut assign: Vec<AssignedState> = Vec::new();
        let mut i = 0;
        #[invariant(loop_invariant, 0 <= @i && @i <= @f.num_vars)]
        #[invariant(length_invariant, (@assign).len() === @i)]
        while i < f.num_vars {
            assign.push(AssignedState::Unset);
            i += 1
        }
        Assignments(assign)
    }

    #[requires(!self.complete())]
    #[ensures(@result < (@self).len())]
    #[ensures((@self)[@result] === AssignedState::Unset)]
    fn find_unassigned(&self) -> usize {
        let mut i = 0;
        #[invariant(loop_invariant, 0 <= @i && @i <= (@self).len())]
        #[invariant(prev, forall<j: Int> 0 <= j && j < @i ==>
            !((@self)[j] === AssignedState::Unset)
        )]
        while i < self.0.len() {
            let curr = self.0[i];
            match curr {
                AssignedState::Unset => {
                    return i;
                },
                _ => {},
            }
            i += 1;
        }
        unreachable!()
    }

    #[predicate]
    fn compatible(self, a2: Assignments) -> bool {
        pearlite! { compatible_inner(@self, @a2) }
    }
}

#[logic]
#[requires(0 <= ix && ix < a.len())]
#[requires(a[ix] === AssignedState::Unset)]
#[requires(eventually_unsat_formula_inner(a.set(ix, AssignedState::Positive), f))]
#[requires(eventually_unsat_formula_inner(a.set(ix, AssignedState::Negative), f))]
#[ensures(eventually_unsat_formula_inner(a, f))]
fn lemma_eventually_assigned(a: Seq<AssignedState>, ix: Int, f: Formula) {
    compatible_inner(a, a.set(ix, AssignedState::Positive));
    compatible_inner(a, a.set(ix, AssignedState::Negative));
}

#[requires(f.invariant())]
#[requires(a.invariant(*f))]
#[ensures(result === true ==> f.eventually_sat(*a))]
#[ensures(result === false ==> f.eventually_unsat(*a))]
fn inner(f: &Formula, a: &Assignments) -> bool {
    match f.eval(a) {
        SatState::Sat => return true,
        SatState::Unsat => return false,
        _ => {}
    };

    let mut a_cloned = a.clone();
    let mut a_cloned2 = a.clone();

    let next = a.find_unassigned();

    a_cloned.0[next] = AssignedState::Positive;
    a_cloned2.0[next] = AssignedState::Negative;

    //proof_assert! { { lemma_eventually_assigned(@a, 0, *f); true }}
    //proof_assert! { a.compatible(a_cloned) };
    //proof_assert! { a.compatible(a_cloned2) };

    if inner(f, &a_cloned) {
        return true;
    } else {
        return inner(f, &a_cloned2);
    }
}
