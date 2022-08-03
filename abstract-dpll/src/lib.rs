use creusot_contracts::*;

struct Literal(Int, bool);

enum Assignment {
    Decision(Literal),
    Justified(Clause, Literal),
}

struct Clause(FSet<Literal>);

struct Formula(FSet<Clause>);

enum Trail {
    Empty,
    Assign(Assignment, Box<Trail>),
}

struct Model(Mapping<Int, bool>);

impl Model {
    #[predicate]
    #[variant(cl.len())]
    fn interp_clause(self, cl: FSet<LiteraL>) -> bool {
        if cl == FSet::EMPTY {
            false
        } else {
            let l = cl.peek();
            self.0.get(l.0) == l.1 || self.interp_clause(cl.remove(l))
        }
    }

    #[predicate]
    #[variant(f.len())]
    fn interp_formula(self, f: FSet<Clause>) -> bool {
        if f == FSet::EMPTY {
            false
        } else {
            let c = f.peek();
            self.interp_clause(c) && self.interp_formula(f.remove(c))
        }
    }

    #[predicate]
    fn satisfies(self, f: Formula) -> bool {
        self.interp_formula(f.0)
    }
}

impl Formula {
    #[predicate]
    fn entails(self, f: Self) -> bool {
        pearlite! {
            forall<m : _> m.satisfies(self) ==> m.satisfies(f)
        }
    }
}

impl Clause {
    #[predicate]
    fn entails(self, c: Self) -> bool {
        pearlite! {
            forall<m : _> m.satisfies(self) ==> m.satisfies(c)
        }
    }
}

impl Formula {
    #[predicate]
    fn invariant(self) -> bool {
        true
    }

    #[predicate]
    fn contains(l : Literal) -> bool {
        false
    }
}

impl Trail {
    #[predicate]
    fn invariant(self) -> bool {
        true
    }

    #[predicate]
    fn contains(self, l : Literal) -> bool {
        false
    }
}

// We characterize DPLL(T) as a two-state transition system, in the normal state
// we perform deductions (unit prop), and make decisions when we get stuck
// When a conflict is detected we can do one of two things depending on the level of the conflict:
// - At level 0 we fail
// - At any other level, we enter the conflict resolution stage
//
// During conflict resolution, we perform a series of resolutions, simplifying
// the conflict clause, and eventually we exit the conflict by backjumping and
// learning a new lemma (explanation).

struct Normal(Trail, Formula);
struct Conflict(Trail, Formula, FSet<Literal>);

impl Normal {
    #[predicate]
    fn invariant(self) -> bool {
        pearlite! { forall<l : _> self.0.contains(l) ==> self.1.contains(l) }
    }
}

impl Conflict {
    #[predicate]
    fn invariant(self) -> bool {
        true
    }
}
// The transition rules of the DPLL(T) system
impl Normal {


    #[logic]
    fn unit_prop(self) -> Self {

    }

    #[logic]
    fn decide(self) -> Self {

    }

    #[predicate]
    fn fail(self) -> bool { false }

    #[logic]
    fn conflict(self) -> Conflict {
        Conflict(self.0, self.1, FSet::EMPTY)
    }
}

impl Conflict {
    #[logic]
    fn resolve(self) -> Self {

    }

    #[logic]
    fn learn_backjump(self) -> Normal {

    }
}