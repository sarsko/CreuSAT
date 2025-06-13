#![allow(unused)] // TODO: remove

struct Lit {
    code: u32,
}

struct Clause {
    clause: Vec<Lit>
}

struct Formula {
    formula: Vec<Clause>,
}

pub type AssignedState = u8;

struct Assignments {
    assignments: Vec<AssignedState>
}