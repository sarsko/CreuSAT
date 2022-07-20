use crate::assignments::AssignedState;
pub(crate) type Cref = usize;

pub enum SatResult {
    Sat(Vec<AssignedState>),
    Unsat,
    Unknown,
    Err,
}

pub(crate) enum ConflictResult {
    Ok,
    Ground,
    Continue,
}
