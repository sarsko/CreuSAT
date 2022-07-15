use creusot_contracts::std::*;
use creusot_contracts::*;

use crate::{assignments::*, clause::*, formula::*, lit::*, trail::*};

use crate::logic::{logic_assignments::*, logic_clause::*, logic_formula::*, logic_trail::*};

#[cfg(feature = "contracts")]
mod inner {
    use creusot_contracts::{*, Model};
    use crate::lit::Lit;
    use crate::formula::Formula;
    use crate::assignments::Assignments;
    pub struct M(Mapping<Int, bool>);

    impl M {
        #[predicate]
        fn satisfies_clause(self, cl: Seq<Lit>) -> bool {
            pearlite! {
                exists<i : Int> 0 <= i && i < cl.len() && self.0.get(@cl[i].idx) == cl[i].polarity
            }
        }

        #[predicate]
        pub fn satisfies(self, fml: Seq<Seq<Lit>>) -> bool {
            pearlite! {
                forall<c : _> 0 <= c && c < fml.len() ==> self.satisfies_clause(fml[c])
            }
        }
    }

    impl Formula {
        #[predicate]
        pub fn unsat(self) -> bool {
            pearlite! { forall<m : M> m.satisfies(self.real_model()) ==> false }
        }

        #[predicate]
        pub fn sat(self) -> bool {
            pearlite! { exists<m : M> m.satisfies(self.real_model()) }
        }

        #[predicate]
        pub fn equisat(self, f: Self) -> bool {
            pearlite! {
                forall<m : M> m.satisfies(self.real_model()) ==> m.satisfies(f.real_model()) && m.satisfies(f.real_model()) ==> m.satisfies(self.real_model())
            }
        }
    }

    impl Assignments {
        #[logic]
        pub fn real_model(self) -> M {
            M(Mapping::cst(false))
        }
    }
}

#[cfg(feature = "contracts")]
pub use inner::*;

#[logic]
fn pos() -> AssignedState {
    1u8
}

#[logic]
fn neg() -> AssignedState {
    0u8
}

#[predicate]
pub fn unset(v: AssignedState) -> bool {
    pearlite! {
        if @v >= 2 {
            true
        } else {
            false
        }
    }
}

#[cfg_attr(feature = "trust_logic_logic", trusted)]
#[logic]
#[ensures(b ==> @result == 1)]
#[ensures(!b ==> @result == 0)]
pub fn bool_to_assignedstate(b: bool) -> AssignedState {
    if b {
        1u8
    } else {
        0u8
    }
}

#[logic]
fn flip_v(v: AssignedState) -> AssignedState {
    pearlite! {
        if @v == 0 {
            1u8
        } else if @v == 1 {
            0u8
        } else {
            v
        }
    }
}
