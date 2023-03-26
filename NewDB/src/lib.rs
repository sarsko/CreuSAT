#![allow(non_snake_case)]
#![allow(unused)]
#![feature(type_ascription)]
#![cfg_attr(not(creusot), feature(stmt_expr_attributes, proc_macro_hygiene))]
extern crate creusot_contracts;

use creusot_contracts::logic::FSet;
use creusot_contracts::{std::clone::Clone, std::*, vec, *};

mod assignments;
mod friday;
mod lit;
mod logic_util;

use crate::{assignments::*, lit::*};

use crate::logic_util::*;

// TODO: Decide on whether to have it as a type or a struct
type CRef = u32;

// TODO: This seems to be a non-ideal invariant
// TODO: Add more
#[predicate]
fn cref_invariant(cref: Int, clause_allocator: ClauseAllocator) -> bool {
    pearlite! {
        cref < (@clause_allocator).len()
        && @(@clause_allocator)[cref].code + cref + @HEADER_LEN <= (@clause_allocator).len()
    }
}

#[derive(Clone)]
struct ClauseAllocator {
    buffer: Vec<Lit>,
}

impl ClauseAllocator {
    #[predicate]
    pub(crate) fn invariant(self) -> bool {
        pearlite! { (@self).len() <= @u32::MAX }
    }

    #[logic]
    //#[requires(cref_invariant(cref, self))]
    pub(crate) fn get_clause_logic(self, cref: Int) -> Seq<Lit> {
        pearlite! {
            (@self).subsequence(cref + @HEADER_LEN, cref + @HEADER_LEN + @((@self)[cref]).code)
        }
    }

    #[logic]
    //#[requires(cref_invariant(cref, self))]
    pub(crate) fn get_clause_fset(self, cref: Int) -> FSet<Lit> {
        pearlite! {
            self.get_clause_fset_internal(cref, cref + @HEADER_LEN, cref + @HEADER_LEN + @((@self)[cref]).code)
        }
    }

    #[logic]
    //#[requires(cref_invariant(cref, self))]
    #[variant(upper - idx)]
    #[requires(idx >= 0 && upper <= (@self).len())]
    fn get_clause_fset_internal(self, cref: Int, idx: Int, upper: Int) -> FSet<Lit> {
        pearlite! {
            if idx < upper {
                let set = self.get_clause_fset_internal(cref, idx + 1, upper);
                set.insert((@self)[cref + idx])
            } else {
                FSet::EMPTY
            }
        }
    }
}

#[cfg(creusot)]
impl ShallowModel for ClauseAllocator {
    type ShallowModelTy = Seq<Lit>;

    #[logic]
    fn shallow_model(self) -> Self::ShallowModelTy {
        self.buffer.shallow_model()
    }
}

const HEADER_LEN: usize = 1;

impl ClauseAllocator {
    #[maintains((mut self).invariant())]
    #[requires((@lits).len() > 0)]
    #[requires((@self).len() + (@lits).len() + @HEADER_LEN <= @u32::MAX)] // TODO: May have to move this to a runtime check
    #[ensures((@^self).len() == (@self).len() + (@lits).len() + @HEADER_LEN)]
    #[ensures(@result == (@self).len())]
    #[ensures(@(@^self)[@result].code == (@lits).len())]
    #[ensures(forall<i: Int> 0 <= i && i < (@self).len() ==> (@^self)[i] == (@self)[i])] // Head unchanged. TODO: Refactor ?
    #[ensures(forall<i: Int> 0 <= i && i < (@lits).len() ==> (@^self)[@result + @HEADER_LEN + i] == (@lits)[i])] // Extended. TODO: Refactor ?
    #[ensures(cref_invariant(@result, ^self))]
    fn add_clause(&mut self, lits: &[Lit]) -> CRef {
        let cref = self.buffer.len() as CRef;
        self.buffer.push(Lit::raw(lits.len() as u32));

        let old_buffer: Ghost<&mut Vec<Lit>> = ghost!(&mut self.buffer);

        #[invariant(vec_proph, ^*old_buffer == (^self).buffer)]
        #[invariant(len, (@self).len() == (@old_buffer).len() + produced.len())]
        #[invariant(head_unchanged, forall<i: Int> 0 <= i && i < (@old_buffer).len() ==> (@self)[i] == (@old_buffer)[i])] // TODO: Refactor ?
        #[invariant(extended, forall<i: Int> 0 <= i && i < (produced).len() ==> (@self)[@cref + @HEADER_LEN + i] == *(produced)[i])]
        for lit in lits {
            self.buffer.push(*lit)
        }

        cref
    }

    #[requires(self.invariant())]
    #[requires(cref_invariant(@cref, *self))]
    #[ensures(@result == self.get_clause_logic(@cref))]
    fn get_clause(&self, cref: u32) -> &[Lit] {
        let idx = cref as usize;
        let len = self.buffer[idx].code as usize;
        &self.buffer[idx + HEADER_LEN..idx + HEADER_LEN + len]
    }
}

struct CRefManager {
    crefs: Vec<CRef>,
}

#[cfg(creusot)]
impl ShallowModel for CRefManager {
    type ShallowModelTy = Seq<CRef>;

    #[logic]
    fn shallow_model(self) -> Self::ShallowModelTy {
        self.crefs.shallow_model()
    }
}

impl CRefManager {
    #[predicate]
    fn invariant(self, clause_allocator: ClauseAllocator) -> bool {
        pearlite! {
            clause_allocator.invariant() &&
            forall<i: Int> 0 <= i && i < (@self).len() ==>
                cref_invariant(@(@self)[i], clause_allocator)
        }
    }

    #[predicate]
    fn are_implied_by(self, original_clauses: CRefManager, clause_allocator: ClauseAllocator) -> bool {
        pearlite! {
            forall<i: Int> 0 <= i && i < (@self).len() ==>
                original_clauses.implies(@(@self)[i], clause_allocator)
        }
    }

    // Does this need the cref invariant again?
    #[predicate]
    fn implies(self: CRefManager, cref: Int, clause_allocator: ClauseAllocator) -> bool {
        pearlite! {
            true
        }
    }
}

struct ClauseManager {
    clause_allocator: ClauseAllocator,
    original_clauses: CRefManager,
    learnt_core: CRefManager,
}

impl ClauseManager {
    #[predicate]
    fn invariant(self) -> bool {
        pearlite! {
            self.clause_allocator.invariant()
            && self.original_clauses.invariant(self.clause_allocator)
            && self.learnt_core.invariant(self.clause_allocator)
            && self.learnt_core.are_implied_by(self.original_clauses, self.clause_allocator)
        }
    }
}

struct Formula {
    formula: FSet<FSet<Lit>>,
}

/*
#[logic]
#[variant(just.len() - ix)]
#[requires(ix >= 0)]
#[requires(forall<i : _> 0 <= i && i < just.len() ==> @just[i] < (@self.assignments).len())]
#[ensures(forall<a : _> result.contains(a) ==> exists<i : _> 0 <= i && i < (@self.assignments).len() && a == (@self.assignments)[i].term_value())]
#[ensures(forall<a : _> result.contains(a) ==> exists<i : _> ix <= i && i < just.len() && a == (@self.assignments)[@just[i]].term_value())]
#[ensures(forall<i : _ > ix <= i && i < just.len() ==> result.contains((@self.assignments)[@just[i]].term_value()))]
pub fn abs_just_inner(self, just: Seq<usize>, ix: Int) -> FSet<(theory::Term, theory::Value)> {
    if ix < just.len() {
        let set = self.abs_just_inner(just, ix + 1);
        let a = (self.assignments.model())[just[ix].model()];
        set.insert((a.term.model(), a.val.model()))
    } else {
        FSet::EMPTY
    }
}
*/

impl Formula {
    // TODO: Look at actually implementing from
    #[logic]
    fn from(crefs: Seq<CRef>, clause_allocator: ClauseAllocator) -> Formula {
        Formula { formula: Formula::from_internal(crefs, clause_allocator, 0) }
    }

    #[logic]
    #[variant((@clause_allocator).len() - idx)]
    #[requires(idx >= 0)]
    #[requires(clause_allocator.invariant())]
    #[requires(forall<i: Int> 0 <= i && i < crefs.len() ==>
                cref_invariant(@crefs[i], clause_allocator))] // CRefManager.invariant unwrapped -> TODO: refactor?
    fn from_internal(crefs: Seq<CRef>, clause_allocator: ClauseAllocator, idx: Int) -> FSet<FSet<Lit>> {
        pearlite! {
            if idx < (@clause_allocator).len() {
                let set = Formula::from_internal(crefs, clause_allocator, idx + 1);
                let clause = clause_allocator.get_clause_fset(@crefs[idx]);
                set.insert(clause)
            } else {
                FSet::EMPTY
            }
        }
    }
}
