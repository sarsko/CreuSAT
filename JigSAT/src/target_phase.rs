use std::vec;

use crate::trail::*;

use rand::prelude::*;

#[derive(Eq, PartialEq, Copy, Clone)]
enum Phase {
    Best,
    Flipped,
    Original,
    Inverted,
    Random,
    Walk,
}

pub(crate) struct TargetPhase {
    polarity: Vec<bool>,
    target_polarity: Vec<u8>, // 0: false, 1: true, 2: unassigned

    next_rephasing: usize,
    best_phase_len: usize,
    best_of_the_best_phase_len: usize, // Lol at this naming. Not used.
    min_len: usize,
    num_rephases: usize,
    cycle: Vec<Phase>,
    best_polarity: Vec<u8>, // 0: false, 1: true, 2: unassign

                            //pub(crate) max_vars_for_walker: usize,
                            //pub(crate) local_search_solver: CCANR,
}

const B: Phase = Phase::Best;
const F: Phase = Phase::Flipped;
const O: Phase = Phase::Original;
const I: Phase = Phase::Inverted;
const R: Phase = Phase::Random;
const W: Phase = Phase::Walk;

impl Default for TargetPhase {
    fn default() -> Self {
        TargetPhase {
            polarity: Vec::new(),
            target_polarity: Vec::new(),

            next_rephasing: 1000,
            best_phase_len: 0,
            best_of_the_best_phase_len: 0,
            min_len: 0,
            num_rephases: 0,
            cycle: vec![B, O, B, I, B, R, B, F], // No walk atm
            best_polarity: Vec::new(),
            //max_vars_for_walker: 70000,
            //pub(crate) local_search_solver: CCANR,
        }
    }
}

impl TargetPhase {
    // We init to all false
    pub(crate) fn new(num_vars: usize) -> Self {
        TargetPhase {
            polarity: vec![false; num_vars],
            target_polarity: vec![0; num_vars],
            best_polarity: vec![0; num_vars],
            min_len: num_vars,
            ..Default::default()
        }

        // TODO: Implement walk and uncomment this
        /*
        if num_vars < 70_000 {
            target_phase.cycle = vec![B, W, B, O, B, I, B, W, B, R, B, F];
        }
        */

    }

    #[inline(always)]
    pub(crate) fn should_rephase(&self, num_conflicts: usize) -> bool {
        self.next_rephasing < num_conflicts
    }

    #[inline]
    pub(crate) fn update_best_phase(&mut self, trail: &Trail) {
        // Just copy assignments verbatim, no?
        let len = trail.trail.len();
        if len < self.min_len && len > 0 {
            self.min_len = len;
        }
        if self.best_phase_len < len {
            for e in self.best_polarity.iter_mut() {
                *e = 2;
            }
            for e in &trail.trail {
                self.best_polarity[e.index()] = e.is_positive() as u8;
            }
            self.best_phase_len = len;
            if self.best_of_the_best_phase_len < self.best_phase_len {
                self.best_of_the_best_phase_len = self.best_phase_len;
            }
        }
    }

    #[inline]
    pub(crate) fn reset(&mut self) {
        if self.cycle[self.num_rephases % self.cycle.len()] != Phase::Best {
            self.num_rephases -= 1;
        }
        self.best_phase_len = 0;
    }

    pub(crate) fn rephase(&mut self, num_conflicts: usize) -> bool {
        let phase = self.cycle[self.num_rephases % self.cycle.len()];
        match phase {
            Phase::Best => {
                println!("c Rephasing to Best");
                for i in 0..self.target_polarity.len() {
                    self.target_polarity[i] = self.best_polarity[i];
                }
            }
            Phase::Flipped => {
                println!("c Rephasing to Flipped");
                // This one differs from Glucose.
                // Glucose does ~e which flips -10 (resulting in 9)
                for e in self.target_polarity.iter_mut() {
                    if *e == 0 {
                        *e = 1;
                    } else if *e == 1 {
                        *e = 0;
                    }
                }
            }
            Phase::Original => {
                println!("c Rephasing to Original");
                for e in self.target_polarity.iter_mut() {
                    *e = 0;
                }
            }
            Phase::Inverted => {
                println!("c Rephasing to Inverted");
                for e in self.target_polarity.iter_mut() {
                    *e = 1;
                }
            }
            Phase::Random => {
                println!("c Rephasing to Random");
                for e in self.target_polarity.iter_mut() {
                    let mut rng = rand::thread_rng();
                    let y: f64 = rng.gen();
                    *e = (y > 0.5) as u8;
                }
            }
            Phase::Walk => {
                println!("c Rephasing to Walk");
                // Restart
                // Run local search solver
                unimplemented!();
            }
        }
        self.num_rephases += 1;
        self.next_rephasing = num_conflicts + self.num_rephases * 1000;
        self.best_phase_len = 0;
        false
    }

    pub(crate) fn choose_polarity(&self, idx: usize, mode_is_focus: bool) -> bool {
        if mode_is_focus || self.target_polarity[idx] == 2 {
            self.polarity[idx]
        } else {
            assert!(self.target_polarity[idx] == 0 || self.target_polarity[idx] == 1);
            self.target_polarity[idx] != 0
        }
    }

    pub(crate) fn set_polarity(&mut self, idx: usize, polarity: bool) {
        self.polarity[idx] = polarity;
    }
}
