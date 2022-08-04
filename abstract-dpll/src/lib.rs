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
    fn satisfy_lit(self, l: Literal) -> bool {
        self.0.get(l.0) == l.1
    }

    #[predicate]
    #[variant(cl.len())]
    fn interp_clause(self, cl: FSet<Literal>) -> bool {
        if cl == FSet::EMPTY {
            false
        } else {
            let l = cl.peek();
            self.satisfy_lit(l) || self.interp_clause(cl.remove(l))
        }
    }

    #[predicate]
    #[variant(f.len())]
    fn interp_formula(self, f: FSet<Clause>) -> bool {
        if f == FSet::EMPTY {
            false
        } else {
            let c = f.peek();
            self.interp_clause(c.0) && self.interp_formula(f.remove(c))
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
            forall<m : self::Model> m.satisfies(self) ==> m.satisfies(f)
        }
    }

    #[predicate]
    fn contains(self, l : Literal) -> bool {
        pearlite! { exists<c : _> self.0.contains(c) && c.0.contains(l) }
    }

    #[predicate]
    fn contains_clause(self, c: Clause) -> bool {
        pearlite! { self.0.contains(c) }
    }
}

impl Clause {
    #[predicate]
    fn contains(self, l : Literal) -> bool {
        self.0.contains(l)
    }

    #[predicate]
    fn entails(self, c: Self) -> bool {
        pearlite! {
            forall<m : self::Model> m.interp_clause(self.0) ==> m.interp_clause(c.0)
        }
    }
}

impl Literal {
    #[logic]
    fn negate(self) -> Self {
        Literal(self.0, !self.1)
    }
}

impl Assignment {
    #[logic]
    fn literal(self) -> Literal {
        match self {
            Assignment::Decision(l) => l,
            Assignment::Justified(_, l) => l,
        }
    }
}
impl Formula {
    #[predicate]
    fn invariant(self) -> bool {
        true
    }
}

impl Trail {
    #[predicate]
    fn invariant(self) -> bool {
        self.trail_unique()
    }

    #[predicate]
    fn trail_unique(self) -> bool {
        match self {
            Trail::Assign(a, tl) => {
                !tl.contains(a.literal()) && !tl.contains(a.literal().negate())
            }
            Trail::Empty => true
        }
    }

    #[predicate]
    fn contains(self, l: Literal) -> bool {
        match self {
            Trail::Assign(Assignment::Decision(l2), tl) => {
                l2 == l || tl.contains(l)
            },
            Trail::Assign(Assignment::Justified(_, l2), tl) => {
                l2 == l || tl.contains(l)
            },
            Trail::Empty => false,
        }
    }

    #[predicate]
    fn models(self, m : self::Model) -> bool {
        match self {
            Trail::Assign(a, tl) => m.satisfy_lit(a.literal()) && tl.models(m),
            Trail::Empty => true
        }
    }

    #[predicate]
    fn unsat(self, c : FSet<Literal>) -> bool {
        pearlite! {
            forall<m : self::Model> self.models(m) ==> !m.interp_clause(c)
        }
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
    #[requires(c.contains(l))]
    #[requires(self.1.contains_clause(c))]
    #[requires(self.0.unsat(c.0.remove(l)))]
    #[requires(!self.0.contains(l))]
    fn unit_prop(self, c: Clause, l : Literal) -> Self {
        Normal(Trail::Assign(Assignment::Justified(c, l), Box::new(self.0)), self.1)
    }

    #[logic]
    #[requires(self.1.contains(l) || self.0.contains(l.negate()))]
    #[requires(!self.0.contains(l))]
    fn decide(self, l: Literal) -> Self {
        Normal(Trail::Assign(Assignment::Decision(l), Box::new(self.0)), self.1)

     }

    #[predicate]
    fn fail(self) -> bool {
        false
    }

    #[logic]
    fn conflict(self) -> Conflict {
        Conflict(self.0, self.1, FSet::EMPTY)
    }
}

impl Conflict {
    #[logic]
    fn resolve(self) -> Self { self }

    #[logic]
    fn learn_backjump(self) -> Normal { Normal(self.0, self.1) }
}
