use creusot_contracts::std::*;
use creusot_contracts::*;

use crate::{assignments::*, clause::*, formula::*, lit::*, trail::*};

use crate::logic::{logic_assignments::*, logic_clause::*, logic_formula::*, logic_trail::*};

#[cfg(feature = "contracts")]
mod inner {
    struct Model(Mapping<Int, bool>);

    impl Model {
        #[predicate]
        fn satisfies_clause(self, cl: Seq<Lit>) -> bool {
            pearlite! {
                forall<i : _> 0 <= i && i < cl.len() ==> self.get(@cl[i].idx) == cl[i].polarity
            }
        }

        #[predicate]
        fn satisfies(self, fml: Seq<Seq<Lit>>) -> bool {
            pearlite! {
                forall<c : _> 0 <= i && i < fml.len() ==> self.satisfies_clause(fml[c])
            }
        }
    }

    impl Formula {
        #[predicate]
        fn unsat(self) -> bool {
            pearlite! { forall<m : Model> m.satisfies(@self) ==> false }
        }

        #[predicate]
        fn sat(self) -> bool {
            pearlite! { exists<m : Model> m.satisfies(@self) }
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
