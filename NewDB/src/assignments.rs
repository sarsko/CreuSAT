use creusot_std::prelude::{Clone, *};

pub type AssignedState = u8;

#[logic]
fn pos() -> AssignedState {
    1u8
}

#[logic]
fn neg() -> AssignedState {
    0u8
}

#[logic]
pub fn unset(v: AssignedState) -> bool {
    pearlite! { v@ >= 2 }
}

pub struct Assignments(pub Vec<AssignedState>);

impl Clone for Assignments {
    #[check(terminates)]
    #[ensures(self@ == result@)]
    fn clone(&self) -> Self {
        Self(self.0.clone())
    }
}

impl View for Assignments {
    type ViewTy = Seq<AssignedState>;

    #[logic]
    fn view(self) -> Self::ViewTy {
        self.0.view()
    }
}

impl Assignments {
    #[logic]
    pub fn inv(self) -> bool {
        pearlite! {
            forall<i: Int> 0 <= i && i < self@.len() ==>
                self@[i]@ < 2
        }
    }
}

#[logic]
pub fn complete_inner(a: Seq<AssignedState>) -> bool {
    pearlite! {
        forall<i: Int> 0 <= i && i < a.len() ==> !unset(a[i])
    }
}
