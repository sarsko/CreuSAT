use crate::{lit::*, solver::Solver, trail::*};
use std::{
    cmp::Ordering,
    ops::{Index, IndexMut},
};

use crate::preprocess::SubsumptionRes;

pub struct Clause {
    pub deleted: bool,
    pub can_be_deleted: bool,
    pub mark: u8, // This is an artifact of Glucose/MiniSat, and should be enumed
    pub lbd: u32,
    pub search: usize,
    abstraction: usize,
    pub lits: Vec<Lit>,
}

impl Index<usize> for Clause {
    type Output = Lit;
    #[inline]
    fn index(&self, i: usize) -> &Lit {
        //#[cfg(feature = "unsafe_access")]
        unsafe { self.lits.get_unchecked(i) }
        //#[cfg(not(feature = "unsafe_access"))]
        //&self.lits[i]
    }
}
impl IndexMut<usize> for Clause {
    #[inline]
    fn index_mut(&mut self, i: usize) -> &mut Lit {
        //#[cfg(feature = "unsafe_access")]
        unsafe { self.lits.get_unchecked_mut(i) }
        //#[cfg(not(feature = "unsafe_access"))]
        //&mut self.lits[i]
    }
}

use std::fmt;

impl fmt::Display for Clause {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let mut to_display = String::from("(");
        let mut first = true;
        for l in &self.lits {
            if !first {
                to_display.push_str(" ∧ ");
            }
            first = false;
            to_display.push_str(&l.to_string());
        }
        to_display.push_str(")");

        write!(f, "{}", to_display)
    }
}

impl fmt::Debug for Clause {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self)
    }
}

impl Clause {
    // Does not set lbd !
    // Inits search to 1 and mark to 0. Sets abstraction.
    pub(crate) fn new(lits: Vec<Lit>) -> Clause {
        Clause {
            deleted: false,
            can_be_deleted: true,
            lbd: 0,
            search: 1,
            mark: 0,
            abstraction: Self::calc_abstraction(&lits),
            lits,
        }
    }

    fn calc_abstraction(lits: &[Lit]) -> usize {
        let mut abstraction = 0;
        for e in lits {
            abstraction |= 1 << (e.index() & 31);
        }
        abstraction
    }

    pub(crate) fn swap(&mut self, i: usize, j: usize) {
        self.lits.swap(i, j);
    }

    pub(crate) fn less_than(&self, other: &Clause) -> Ordering {
        if self.len() == 2 {
            if other.len() == 2 {
                Ordering::Equal
            } else {
                Ordering::Less
            }
        } else if other.len() == 2 {
            Ordering::Greater
        } else if self.lbd < other.lbd {
            Ordering::Less
        } else if self.lbd > other.lbd {
            Ordering::Greater
        } else if self.len() < other.len() {
            Ordering::Less
        } else if self.len() > other.len() {
            Ordering::Greater
        } else {
            Ordering::Equal
        }
    }

    pub(crate) fn check_clause_invariant(&self, n: usize) -> bool {
        let mut i: usize = 0;
        while i < self.len() {
            if !self[i].check_lit_invariant(n) {
                return false;
            }
            i += 1;
        }
        if self.no_duplicates() {
            return true;
        }
        false
    }

    pub(crate) fn no_duplicates(&self) -> bool {
        let mut i: usize = 0;
        while i < self.len() {
            let lit1 = self[i];
            let mut j: usize = 0;
            while j < i {
                let lit2 = self[j];
                if lit1.index() == lit2.index() {
                    return false;
                }
                j += 1;
            }
            i += 1;
        }
        true
    }

    #[inline(always)]
    pub(crate) fn len(&self) -> usize {
        self.lits.len()
    }

    fn calc_lbd(&self, trail: &Trail, solver: &mut Solver) -> u32 {
        /*
        // We don't bother calculating for long clauses.
        if self.len() >= 2024 {
            return 2024;
        }
        */
        let mut lbd: u32 = 0;
        for l in &self.lits {
            let level = trail.lit_to_level[l.index()];
            if solver.perm_diff[level as usize] != solver.num_conflicts {
                solver.perm_diff[level as usize] = solver.num_conflicts;
                lbd += 1;
            }
        }
        lbd
    }

    pub(crate) fn calc_and_set_lbd(&mut self, trail: &Trail, solver: &mut Solver) {
        self.lbd = self.calc_lbd(trail, solver);
    }

    fn calc_and_set_abstraction(&mut self) {
        self.abstraction = Clause::calc_abstraction(&self.lits);
    }
}

// Only used in preprocessing
impl Clause {
    fn incompatible_abstract_levels(&self, other: &Clause) -> bool {
        //debug!("Incompat abstract");
        self.abstraction & !other.abstraction != 0
    }

    pub(crate) fn subsumes(&self, other: &Clause) -> SubsumptionRes {
        // if (other.size() < size() || (extra.abst & ~other.extra.abst) != 0)
        // if (other.size() < size() || (!learnt() && !other.learnt() && (extra.abst & ~other.extra.abst) != 0))
        /*
        assert(!header.learnt);
        assert(!other.header.learnt);
        assert(header.has_extra);
        assert(other.header.has_extra);
        */
        // What is happening here?
        // If the abstraction level of this clause (which I assume is stored at the end of the lits) ANDed with the NOT
        // of the abstraction level of the other clause are different, then return?
        // Why in the world is the abstraction level stored as at the end instead of in the header?
        // Also, why isnt the abstraction() call used?
        // Aha, because for learns we use header.size and header.size + 1 to store act and touched, but for
        // non-learnts (I'm assuming this means input clauses), we store abstraction in header.size.
        if other.len() < self.len() || self.incompatible_abstract_levels(other) {
            return SubsumptionRes::NoSubsumption;
        }

        let mut ret = SubsumptionRes::Subsumed;

        'outer: for s in &self.lits {
            // search for c[i] or ~c[i]
            for o in &other.lits {
                if s == o {
                    continue 'outer;
                } else if ret == SubsumptionRes::Subsumed && *s == !*o {
                    ret = SubsumptionRes::RemoveLit(*s);
                    continue 'outer;
                }
            }
            return SubsumptionRes::NoSubsumption;
        }
        ret
    }

    pub(crate) fn is_marked(&self) -> bool {
        self.mark > 0
    }

    pub(crate) fn get_mark(&self) -> u8 {
        self.mark
    }

    pub(crate) fn set_mark(&mut self, new_val: u8) {
        self.mark = new_val;
    }

    // Requires that the lit is in the clause
    // Requires that the clause is not watched
    fn remove(&mut self, lit: Lit) {
        for (i, l) in self.lits.iter().enumerate() {
            if *l == lit {
                self.lits.swap_remove(i);
                return;
            }
        }
    }

    pub(crate) fn strengthen(&mut self, p: Lit) {
        self.remove(p);
        self.calc_and_set_abstraction();
    }
}
