use crate::lit::Lit;
use crate::clause_manager::{common::CRef, clause_allocator::ClauseAllocator, cref_manager::CRefManager};
use crate::solver::Solver;
use crate::trail::Trail;
use crate::watches::{Watches, Watcher};

/// The `ClauseManager` wraps a `ClauseAllocator` and a series of `CRefManager`s.
/// The `ClauseAllocator` is a linear buffer of `Lit`s in the format:
/// [S, H, L_0, ..., L_S],
/// where "S" is the clause size, "H" is the clause header and
/// L_0 to L_S are the lits in the clause.
/// H follows the clause header format TODO.
/// The lits follows the encoding described in [lit.rs)[lit.rs] TODO.
pub struct ClauseManager {
    clause_allocator: ClauseAllocator,
    original_clauses: CRefManager,
    learnt_core: CRefManager,
    learnt_local: CRefManager,
    learnt_tier: CRefManager,
    pub num_vars: usize,
    cur_restart: usize,
    num_clauses_before_reduce: usize,
    special_inc_reduce_db: usize,

    next_tier_reduce: usize,
    next_local_reduce: usize,
    pub(crate) core_upper_bound: u32,
    tiers_upper_bound: u32,
    clause_activity_inc: f64,
    clause_decay: f64,

    // Stats
    pub(crate) num_reduced: usize,
    pub(crate) num_deleted_clauses: usize,
}

impl ClauseManager {
    // TODO: Swap to a builder scheme where num_vars is generated afterwards?
    pub fn new(num_vars: usize) -> Self {
        Self {
            clause_allocator: ClauseAllocator::new(),
            original_clauses: CRefManager::new(),
            learnt_core: CRefManager::new(),
            learnt_local: CRefManager::new(),
            learnt_tier: CRefManager::new(),
            num_vars,
            cur_restart: 1,
            num_clauses_before_reduce: 2000,
            special_inc_reduce_db: 1000,
            next_tier_reduce: 10_000,
            next_local_reduce: 15_000,
            core_upper_bound: 3,
            tiers_upper_bound: 6,
            clause_activity_inc: 1.0,
            clause_decay: 0.999,

            // Stats
            num_reduced: 0,
            num_deleted_clauses: 0,
        }

    }
    
    pub(crate) fn learn_clause(&mut self, lits: &[Lit], watches: &mut Watches, lbd: u32) -> CRef {
        // The weird assignment to first_/second_lit is because otherwise we break the precond for
        // add_watcher that the cref should be less than f.len(). We can't update the watches
        // after the clause is added, as the value gets moved by the push. Could of course index on last
        // element of f after the push, but I prefer this.
        let first_lit = lits[0];
        let second_lit = lits[1];
        let cref = self.clause_allocator.add_clause(lits, lbd);
        watches[first_lit.to_neg_watchidx()].push(Watcher { cref, blocker: second_lit });
        watches[second_lit.to_neg_watchidx()].push(Watcher { cref, blocker: first_lit });

        self.learnt_core.add_cref(cref);

        cref
    }

    pub(crate) fn add_clause_parser(&mut self, lits: &[Lit]) -> CRef {
        let cref = self.clause_allocator.add_clause_parser(lits);
        self.original_clauses.add_cref(cref);
        cref
    }

    // TODO: Unsure whether this scheme or implementing iter/iter_mut etc is the better scheme
    pub(crate) fn original_crefs(&self) -> &[CRef] {
        &self.original_clauses.crefs
    }

    pub(crate) fn get_clause(&self, cref: CRef) -> &[Lit] {
        self.clause_allocator.get_clause(cref)
    }

    pub(crate) fn get_clause_mut(&mut self, cref: CRef) -> &mut [Lit] {
        self.clause_allocator.get_clause_mut(cref)
    }

    pub(crate) fn get_clause_len(&self, cref: CRef) -> u32 {
        self.clause_allocator.get_len(cref)
    }

    pub(crate) fn get_first_lit(&self, cref: CRef) -> Lit {
        self.clause_allocator.get_first_lit(cref)
    }

    pub(crate) fn original_len(&self) -> usize {
        self.original_clauses.len()
    }

    // TODO: Reevaluate the entire scheme of wrappers and tiny functions
    /// NOTE: `cref` has to be a valid `CRef` (pointing to the zeroth clause header literal)
    pub(crate) fn get_search(&self, cref: CRef) -> u8 {
        self.clause_allocator.get_lit(cref + 1).get_search() + 1
    }

    /// NOTE: `cref` has to be a valid `CRef` (pointing to the zeroth clause header literal)
    pub(crate) fn get_lbd(&self, cref: CRef) -> u32 {
        self.clause_allocator.get_lit(cref + 1).get_raw()
    }

    /// NOTE: `cref` has to be a valid `CRef` (pointing to the zeroth clause header literal)
    pub(crate) fn set_search(&mut self, cref: CRef, new_search: u8) {
        self.clause_allocator.get_lit_mut(cref + 1).set_search(new_search - 1);
    }

    // TODO: Implement (currently not incorrect, though bad)
    pub(crate) fn collect_garbage_on_empty_trail(&mut self, watches: &mut Watches, solver: &Solver) {
        
    }

    // TODO: Have to change this once we have multiple tiers of learnt clauses
    pub(crate) fn trigger_reduce(&mut self, num_conflicts: usize) -> bool {
        if num_conflicts >= (self.cur_restart * self.num_clauses_before_reduce) && self.learnt_core.len() > 500 {
            self.cur_restart = (num_conflicts / self.num_clauses_before_reduce) + 1;
            return true;
        }
        false
    }

    #[inline]
    pub(crate) fn reduceDB(&mut self, watches: &mut Watches, trail: &Trail, solver: &mut Solver) {
        // TODO: Is this needed ? Do we ever call `reduceDB` with empty learnts ?
        if self.learnt_core.len() == 0 {
            return;
        }
        self.learnt_core.crefs.sort_unstable_by(|a, b| self.clause_allocator.clause_less_than(*a, *b));
        //s.max_len += self.len() + 300;
        //self.num_reduced += 1;
        let mut limit = self.learnt_core.len() / 2;
        if self.get_lbd(self.learnt_core[limit]) <= 3 {
            self.num_clauses_before_reduce += self.special_inc_reduce_db;
        }

        if self.get_lbd(self.learnt_core[self.learnt_core.len() - 1]) <= 5 {
            self.num_clauses_before_reduce += self.special_inc_reduce_db;
        }

        // TODO: This is a for-loop and is slightly different in Glucose -- revisit and check what is better
        let mut i = 0;
        while i < self.learnt_core.len() && limit > 0 {
            let cref = self.learnt_core[i];
            let mut clause_header = self.clause_allocator.get_clause_header(cref);
            if clause_header.get_lbd() > 2 && clause_header.get_len() > 2 && clause_header.can_be_deleted() {
                //&& !trail.locked(clause[0]) {
                // unwatch_and_mark_as_deleted inlined
                clause_header.mark_clause_as_deleted();
                watches.unwatch(cref, self.clause_allocator.get_first_lit(cref));
                watches.unwatch(cref, self.clause_allocator.get_second_lit(cref));

                // TODO: We don't currently track number of removed clauses, but could
                // solver.num_removed += 1;

                // TODO This does cause a premature visit to the cref at the end
                self.learnt_core.crefs.swap_remove(i);
                limit -= 1;
            } else {
                // TODO: This is new, gotta check whether it works correctly in the edge cases
                if !clause_header.can_be_deleted() {
                    limit += 1;
                }
                clause_header.set_can_be_deleted();
                i += 1;
            }
        }

        /*
        if self.time_for_garbage_collection() {
            self.collect_garbage();
        }
        */
    }
}