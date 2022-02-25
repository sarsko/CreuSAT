use crate::clause::*;

#[derive(Clone, Copy, Eq, PartialEq, Debug)]
pub struct Lit {
    pub idx: usize,
    pub polarity: bool,
}
