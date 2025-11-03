use creusot_contracts::prelude::{Clone, *};

pub type AssignedState = u8;

#[logic(open)]
fn pos() -> AssignedState {
    1u8
}

#[logic(open)]
fn neg() -> AssignedState {
    0u8
}

#[logic(open)]
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

    #[logic(open)]
    fn view(self) -> Self::ViewTy {
        self.0.view()
    }
}

impl Assignments {
    #[logic(open)]
    pub fn inv(self) -> bool {
        pearlite! {
            forall<i: Int> 0 <= i && i < self@.len() ==>
                self@[i]@ < 2
        }
    }
}

#[logic(open)]
pub fn complete_inner(a: Seq<AssignedState>) -> bool {
    pearlite! {
        forall<i: Int> 0 <= i && i < a.len() ==> !unset(a[i])
    }
}
