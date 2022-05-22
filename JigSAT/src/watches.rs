use crate::{formula::*, lit::*, trail::*, solver::*};

// Lets try this scheme and see how well it fares
// Watches are indexed on 2 * lit.idx for positive and 2 * lit.idx + 1 for negative
pub struct Watcher {
    pub cref: usize,
    //blocker: Lit,
}

pub struct Watches {
    pub watches: Vec<Vec<Watcher>>,
}

pub fn update_watch(f: &Formula, trail: &Trail, watches: &mut Watches, cref: usize, j: usize, k: usize, lit: Lit) {
    let watchidx = lit.to_watchidx();
    let end = watches.watches[watchidx].len() - 1;
    watches.watches[watchidx].swap(j, end);
    let curr_lit = f.clauses[cref][k];
    match watches.watches[watchidx].pop() {
        Some(w) => {
            watches.watches[curr_lit.to_neg_watchidx()].push(w);
        }
        None => {
            unreachable!();
        }
    }
}


impl Watches {
    pub fn new(f: &Formula) -> Watches {
        let mut i: usize = 0;
        let mut watches = Vec::new();
        while i < f.num_vars {
            watches.push(Vec::new());
            watches.push(Vec::new());
            i += 1;
        }
        Watches { watches }
    }

    pub fn add_watcher(&mut self, lit: Lit, cref: usize, _f: &Formula) {
        self.watches[lit.to_neg_watchidx()].push(Watcher { cref });
    }

    pub fn move_to_end(&mut self, old_idx: usize, old_pos: usize, new_lit: Lit, _f: &Formula) {
        let end = self.watches[old_idx].len() - 1;
        self.watches[old_idx].swap(old_pos, end);
    }

    pub fn init_watches(&mut self, f: &Formula) {
        let mut i = 0;
        while i < f.clauses.len() {
            let clause = &f.clauses[i];
            if clause.len() > 1 {
                self.add_watcher(clause[0], i, f);
                self.add_watcher(clause[1], i, f);
            }
            i += 1;
        }
    }

    pub fn unwatch(&mut self, f: &Formula, trail: &Trail, cref: usize, lit: Lit) {
        let watchidx = lit.to_neg_watchidx();
        let mut i: usize = 0;
        while i < self.watches[watchidx].len() {
            if self.watches[watchidx][i].cref == cref {
                let end = self.watches[watchidx].len() - 1;
                self.watches[watchidx].swap(i, end);
                match self.watches[watchidx].pop() {
                    Some(w) => {
                    }
                    None => {
                        unreachable!();
                    }
                }
                return;
            }
            i += 1;
        }
    }

    pub fn unwatch_all_lemmas(&mut self, f: &Formula, s: &Solver) {
        let mut i: usize = 0;
        while i < self.watches.len() {
            let mut j = 0;
            while j < self.watches[i].len() {
                if self.watches[i][j].cref > s.initial_len {
                    let end = self.watches[i].len() - 1;
                    self.watches[i].swap(j, end);
                    self.watches[i].pop();
                } else {
                    j += 1;
                }
            }
            i += 1;
        }
    }
}
