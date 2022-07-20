use crate::{lit::*, solver::Solver, trail::*};

use crate::preprocess::SubsumptionRes;

/*
pub struct Clause {
    deleted: bool,
    can_be_deleted: bool,
    mark: u8, // This is an artifact of Glucose/MiniSat, and should be enumed
    lbd: u32,
    search: usize,
    abstraction: usize,
    lits: Vec<Lit>,
}
*/

// HEADER:
// deleted: 1, can_be_deleted: 1, mark:

pub struct Clause {
    //lits: &'a [Lit],
}

/*
impl Index<usize> for Clause<'_> {
    type Output = Lit;
    #[inline]
    fn index(&self, i: usize) -> &Lit {
        //#[cfg(feature = "unsafe_access")]
        unsafe { self.lits.get_unchecked(i) }
        //#[cfg(not(feature = "unsafe_access"))]
        //&self.lits[i]
    }
}
impl IndexMut<usize> for Clause<'_> {
    #[inline]
    fn index_mut(&mut self, i: usize) -> &mut Lit {
        //#[cfg(feature = "unsafe_access")]
        unsafe { self.lits.get_unchecked_mut(i) }
        //#[cfg(not(feature = "unsafe_access"))]
        //&mut self.lits[i]
    }
}
*/

/*
use std::fmt;

impl fmt::Display for Clause<'_> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let mut to_display = String::from("(");
        let mut first = true;
        for l in self.get_literals() {
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

impl fmt::Debug for Clause<'_> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self)
    }
}
*/

impl Clause {
    // Does not set lbd !
    // Inits search to 1 and mark to 0. Sets abstraction.
    /*
    pub(crate) fn new(lits: Vec<Lit>) -> Clause<'_> {
        let mut header = Vec::from(Self::create_header(&lits));
        header.extend(lits);
        Clause {
            lits: header,
        }
    }
    */

    #[inline]
    pub(crate) fn create_header(lits: &[Lit], lbd: u32) -> [Lit; 2] {
        let mut header = ZERO_LIT;
        //header.set_deleted(false);
        header.set_can_be_deleted();
        header.set_fresh_lbd(lbd);
        //header.set_lbd(
        //header.set_search(
        let size = Lit::raw(lits.len() as u32);
        assert!(size.get_len_from_header_lit() as usize == lits.len());
        [header, size]
        /*
        deleted: false,
        can_be_deleted: true,
        lbd: 0,
        search: 1,
        mark: 0,
        abstraction: Self::calc_abstraction(&lits),
        */
    }

    fn calc_abstraction(lits: &[Lit]) -> usize {
        let mut abstraction = 0;
        for e in lits {
            abstraction |= 1 << (e.index() & 31);
        }
        abstraction
    }

    /*
    pub(crate) fn swap(&mut self, i: usize, j: usize) {
        self.lits.swap(i, j);
    }
    */

    /*
    pub(crate) fn pop(&mut self) {
        self.lits.pop();
    }
    */

    /*
    deleted: bool,
    can_be_deleted: bool,
    mark: u8, // This is an artifact of Glucose/MiniSat, and should be enumed
    lbd: u32,
    search: usize,
    abstraction: usize,
    lits: Vec<Lit>,
    */

    /*

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
    */

    /*
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
    */

    /*
    #[inline(always)]
    pub(crate) fn len(&self) -> usize {
        self.lits.len()
    }
    */

    /*
    #[inline(always)]
    fn move_to_end(&mut self, idx: usize, _f: &Formula) {
        let end = self.len() - 1;
        self.swap(idx, end);
    }
    */

    /*
    #[inline(always)]
    pub(crate) fn remove_from_clause(&mut self, idx: usize, _f: &Formula) {
        self.move_to_end(idx, _f);
        self.pop();
    }
    */

    pub(crate) fn calc_lbd(lits: &[Lit], trail: &Trail, solver: &mut Solver) -> u32 {
        /*
        // We don't bother calculating for long clauses.
        if self.len() >= 2024 {
            return 2024;
        }
        */
        let mut lbd: u32 = 0;
        for l in lits {
            let level = trail.lit_to_level[l.index()];
            if solver.perm_diff[level as usize] != solver.num_conflicts {
                solver.perm_diff[level as usize] = solver.num_conflicts;
                lbd += 1;
            }
        }
        lbd
    }

    /*
    pub(crate) fn calc_and_set_lbd(&mut self, trail: &Trail, solver: &mut Solver) {
        let lbd = self.calc_lbd(trail, solver);
        self.get_header().set_lbd(lbd);
    }
    */

    /*
    fn get_header(&mut self) -> &mut Lit {
        &mut self.lits[0]
    }
    */

    fn calc_and_set_abstraction(&mut self) {
        unimplemented!()
        //self.abstraction = Clause::calc_abstraction(&self.lits);
    }
}

// Only used in preprocessing
/*
impl Clause {
    fn incompatible_abstract_levels(&self, other: &Clause) -> bool {
        //debug!("Incompat abstract");
        unimplemented!()
        //self.abstraction & !other.abstraction != 0
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

        'outer: for s in self.get_literals() {
            // search for c[i] or ~c[i]
            for o in self.get_literals() {
                if s == o {
                    continue 'outer;
                } else if ret == SubsumptionRes::Subsumed && *s == !*o {
                    ret = SubsumptionRes::RemoveLit(*s);
                    continue 'outer;
                }
            }
            return SubsumptionRes::NoSubsumption;
        }
        return ret;
    }

    pub(crate) fn is_marked(&self) -> bool {
        unimplemented!()
        //self.get_mark() > 0
    }

    pub(crate) fn get_mark(&self) -> u8 {
        unimplemented!()
        //self.mark
    }

    pub(crate) fn set_mark(&mut self, new_val: u8) {
        unimplemented!()
        //self.mark = new_val;
    }

    // Requires that the lit is in the clause
    // Requires that the clause is not watched
    fn remove(&mut self, lit: Lit) {
        /*
        for (i, l) in self.get_literals().iter().enumerate() {
            if *l == lit {
                self.lits.swap_remove(i);
                return;
            }
        }
        */
    }

    pub(crate) fn strengthen(&mut self, p: Lit) {
        self.remove(p);
        self.calc_and_set_abstraction();
    }
}

impl ClauseTrait for Clause<'_> {
    fn is_deleted(&self) -> bool {
        unimplemented!()
        //self.deleted
    }

    fn can_be_deleted(&self) -> bool {
        unimplemented!()
        //self.can_be_deleted
    }

    fn get_mark(&self) -> u8 {
        unimplemented!()
        //self.mark
    }

    fn get_lbd(&self) -> u32 {
        unimplemented!()
        //self.lbd
    }

    fn get_search_index(&self) -> usize {
        unimplemented!()
        //self.search
    }

    fn set_search_index(&mut self, new_idx: usize) {
        unimplemented!()
        //self.search = new_idx;
    }

    fn get_abstraction(&self) -> usize {
        unimplemented!()
        //self.abstraction
    }

    fn get_literals(&self) -> &[Lit] {
        &self.lits[1..]
    }

    fn set_deleted(&mut self, new_val: bool) {
        unimplemented!()
        //self.deleted = new_val;
    }
}

pub(crate) trait ClauseTrait {
    fn is_deleted(&self) -> bool;

    fn can_be_deleted(&self) -> bool;

    fn set_deleted(&mut self, new_val: bool);

    fn get_mark(&self) -> u8; // TODO: enum

    fn get_lbd(&self) -> u32;

    fn get_search_index(&self) -> usize;

    fn set_search_index(&mut self, new_idx: usize);

    fn get_abstraction(&self) -> usize;

    fn get_literals(&self) -> &[Lit];
}
*/
