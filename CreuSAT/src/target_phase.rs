extern crate creusot_contracts;
use ::std::num;

use creusot_contracts::logic::Ghost;
use creusot_contracts::std::*;
use creusot_contracts::*;

//use std::vec;

use crate::{trail::*, formula::*};

//use rand::prelude::*;

use creusot_contracts::derive::Clone;
use creusot_contracts::derive::PartialEq;

//#[derive(Eq, PartialEq, Copy, Clone)]
#[derive(Copy, Clone)]
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
    //best_of_the_best_phase_len: usize, // Lol at this naming. Not used.
    min_len: usize,
    num_rephases: usize,
    cycle: Vec<Phase>,
    best_polarity: Vec<u8>, // 0: false, 1: true, 2: unassign

                            //pub(crate) max_vars_for_walker: usize,
                            //pub(crate) local_search_solver: CCANR,
}

/*
const B: Phase = Phase::Best;
const F: Phase = Phase::Flipped;
const O: Phase = Phase::Original;
const I: Phase = Phase::Inverted;
const R: Phase = Phase::Random;
const W: Phase = Phase::Walk;
*/

#[cfg_attr(not(untrust_perm), trusted)]
#[ensures(@l <= @result && @result  < @u)]
fn rand_in_range(l: usize, u: usize) -> u8 {
    use rand::Rng;
    let n = rand::thread_rng().gen_range(l..u);
    n as u8
}

fn flip(num: u8) -> u8 {
    if num == 0 {
        return 1;
    } else if num == 1 {
        return 0;
    }
    num
}


impl Default for TargetPhase {
    #[ensures((@result.cycle).len() > 0)]
    fn default() -> Self {
        let mut cycle = Vec::new();
        cycle.push(Phase::Best);
        cycle.push(Phase::Original);
        cycle.push(Phase::Best);
        cycle.push(Phase::Inverted);
        cycle.push(Phase::Best);
        cycle.push(Phase::Random);
        cycle.push(Phase::Best);
        cycle.push(Phase::Flipped);

        TargetPhase {
            polarity: Vec::new(),
            target_polarity: Vec::new(),

            next_rephasing: 1000,
            best_phase_len: 0,
            //best_of_the_best_phase_len: 0,
            min_len: 0,
            num_rephases: 0,
            //cycle: vec![B, O, B, I, B, R, B, F], // No walk atm
            cycle,
            best_polarity: Vec::new(),
            //max_vars_for_walker: 70000,
            //pub(crate) local_search_solver: CCANR,
        }
    }
}


impl TargetPhase {
    /*
    #[predicate]
    pub fn invariant(self) -> bool {
        pearlite! {
            (@self.polarity).len() == @self.num_vars
            && (@self.polarity).len() == @self.num_vars
            && (@self.target_polarity).len() == @self.num_vars
            && (@self.best_polarity).len() == @self.num_vars
        }
    }
    */

    #[predicate]
    pub fn invariant(self, num_vars: Int) -> bool {
        pearlite! {
               (@self.polarity).len() == num_vars
            && (@self.polarity).len() == num_vars
            && (@self.target_polarity).len() == num_vars
            && (@self.best_polarity).len() == num_vars
            && (@self.cycle).len() > 0
        }
    }
}

impl TargetPhase {
    //#[trusted]
    #[requires((@self.cycle).len() > 0)]
    #[ensures(@result < (@self.cycle).len())]
    fn modulo(&self) -> usize {
        self.num_rephases % self.cycle.len()
    }

    // We init to all false
    #[ensures(result.invariant(@num_vars))]
    pub(crate) fn new(num_vars: usize) -> Self {
        let mut target_phase = TargetPhase::default();
        target_phase.polarity = vec![false; num_vars];
        target_phase.target_polarity = vec![0; num_vars];
        target_phase.best_polarity = vec![0; num_vars];
        target_phase.min_len = num_vars;

        // TODO: Implement walk and uncomment this
        /*
        if num_vars < 70_000 && false {
            target_phase.cycle = vec![B, W, B, O, B, I, B, W, B, R, B, F];
        }
        */

        target_phase
    }

    #[inline(always)]
    pub(crate) fn should_rephase(&self, num_conflicts: usize) -> bool {
        self.next_rephasing < num_conflicts
    }

    #[inline]
    #[maintains((mut self).invariant(@_f.num_vars))]
    fn reset_best_polarity(&mut self, _f: &Formula) {
        let old_self: Ghost<&mut TargetPhase> = ghost!(self);
        let mut i: usize = 0;
        #[invariant(i_less, @i <= (@self.best_polarity).len())]
        #[invariant(inv, self.invariant(@_f.num_vars))]
        #[invariant(proph, ^old_self.inner() == ^self)]
        while i < self.best_polarity.len() {
            self.best_polarity[i] = 2;
            i += 1;
        }
    }

    #[inline]
    #[requires(trail.invariant(*_f))]
    #[maintains((mut self).invariant(@_f.num_vars))]
    fn set_best_polarity(&mut self, trail: &Trail, _f: &Formula) {
        let old_self: Ghost<&mut TargetPhase> = ghost!(self);
        let mut i: usize = 0;
        #[invariant(i_less, @i <= (@trail.trail).len())]
        #[invariant(inv, self.invariant(@_f.num_vars))]
        #[invariant(proph, ^old_self.inner() == ^self)]
        while i < trail.trail.len() {
            //self.best_polarity[e.lit.index()] = e.lit.is_positive() as u8;
            let lit = trail.trail[i].lit;
            if lit.is_positive() {
                self.best_polarity[lit.index()] = 1;
            } else {
                self.best_polarity[lit.index()] = 0;
            }
            i += 1;
        }
    }

    #[inline]
    #[requires(trail.invariant(*_f))]
    #[maintains((mut self).invariant(@_f.num_vars))]
    //#[requires(@self.num_vars == @_f.num_vars)]
    //#[ensures(@(^self).num_vars == @_f.num_vars)]
    pub(crate) fn update_best_phase(&mut self, trail: &Trail, _f: &Formula) {
        //let old_self: Ghost<&mut TargetPhase> = ghost!(self);
        // Just copy assignments verbatim, no?
        let len = trail.trail.len();
        if len < self.min_len && len > 0 {
            self.min_len = len;
        }
        if self.best_phase_len < len {
            self.reset_best_polarity(_f);
            self.set_best_polarity(trail, _f);

            self.best_phase_len = len;
            /*
            if self.best_of_the_best_phase_len < self.best_phase_len {
                self.best_of_the_best_phase_len = self.best_phase_len;
            }
            */
        }
    }

    #[inline]
    #[maintains((mut self).invariant(@_f.num_vars))]
    pub(crate) fn reset(&mut self, _f: &Formula) {
        let modulo = self.modulo();
        match self.cycle[modulo] {
            Phase::Best => {},
            _ => {
                if self.num_rephases > 0 {
                    self.num_rephases -= 1;
                }
            }
        }
        self.best_phase_len = 0;
    }

    #[maintains((mut self).invariant(@_f.num_vars))]
    pub(crate) fn rephase(&mut self, num_conflicts: usize, _f: &Formula) -> bool {
        let old_self: Ghost<&mut TargetPhase> = ghost!(self);
        let phase = self.cycle[self.modulo()];
        match phase {
            Phase::Best => {
                //println!("c Rephasing to Best");
                //for i in 0..self.target_polarity.len() {
                let mut i: usize = 0;
                #[invariant(i_less, @i <= (@self.target_polarity).len())]
                //#[invariant(i_less2, @i <= (@self.best_polarity).len())]
                #[invariant(inv, self.invariant(@_f.num_vars))]
                //#[invariant(unch, @old_self.inner().num_vars == @self.num_vars)]
                #[invariant(proph, ^old_self.inner() == ^self)]
                while i < self.target_polarity.len() {
                    self.target_polarity[i] = self.best_polarity[i];
                    i += 1;
                }
            }
            Phase::Flipped => {
                //println!("c Rephasing to Flipped");
                // This one differs from Glucose.
                // Glucose does ~e which flips -10 (resulting in 9)
                let mut i: usize = 0;
                #[invariant(i_less, @i <= (@self.target_polarity).len())]
                #[invariant(inv, self.invariant(@_f.num_vars))]
                #[invariant(proph, ^old_self.inner() == ^self)]
                while i < self.target_polarity.len() {
                    self.target_polarity[i] = flip(self.target_polarity[i]);
                    /*
                    if self.target_polarity[i] == 0 {
                        self.target_polarity[i] = 1;
                    } else if self.target_polarity[i] == 1 {
                        self.target_polarity[i] = 0;
                    }
                    */
                    i += 1;
                }
                /*
                for e in self.target_polarity.iter_mut() {
                    if *e == 0 {
                        *e = 1;
                    } else if *e == 1 {
                        *e = 0;
                    }
                }
                */
            }
            Phase::Original => {
                //println!("c Rephasing to Original");
                /*
                for e in self.target_polarity.iter_mut() {
                    *e = 0;
                }
                */
                let mut i: usize = 0;
                #[invariant(i_less, @i <= (@self.target_polarity).len())]
                #[invariant(inv, self.invariant(@_f.num_vars))]
                #[invariant(proph, ^old_self.inner() == ^self)]
                while i < self.target_polarity.len() {
                   self.target_polarity[i] = 0;
                   i += 1;
                }
            }
            Phase::Inverted => {
                //println!("c Rephasing to Inverted");
                /*
                for e in self.target_polarity.iter_mut() {
                    *e = 1;
                }
                */
                let mut i: usize = 0;
                #[invariant(i_less, @i <= (@self.target_polarity).len())]
                #[invariant(inv, self.invariant(@_f.num_vars))]
                #[invariant(proph, ^old_self.inner() == ^self)]
                while i < self.target_polarity.len() {
                   self.target_polarity[i] = 1;
                   i += 1;
                }
            }
            Phase::Random => {
                //println!("c Rephasing to Random");
                /*
                for e in self.target_polarity.iter_mut() {
                    let mut rng = rand::thread_rng();
                    let y: f64 = rng.gen();
                    *e = (y > 0.5) as u8;
                }
                */

                let mut i: usize = 0;
                #[invariant(i_less, @i <= (@self.target_polarity).len())]
                #[invariant(inv, self.invariant(@_f.num_vars))]
                #[invariant(proph, ^old_self.inner() == ^self)]
                while i < self.target_polarity.len() {
                   self.target_polarity[i] = rand_in_range(0, 2);
                   i += 1;
                }
            }
            Phase::Walk => {
                //println!("c Rephasing to Walk");
                // Restart
                // Run local search solver
                //unimplemented!();
            }
        }
        if self.num_rephases < usize::MAX {
            self.num_rephases += 1;
        }
        if self.num_rephases < usize::MAX / 1000 {
            if self.num_rephases * 1000 < usize::MAX - num_conflicts {
                self.next_rephasing = num_conflicts + self.num_rephases * 1000;
            }
        }
        self.best_phase_len = 0;
        false
    }

    #[requires((@self.polarity).len() > @idx)]
    #[requires((@self.target_polarity).len() > @idx)]
    pub(crate) fn choose_polarity(&self, idx: usize, mode_is_focus: bool) -> bool {
        if mode_is_focus || self.target_polarity[idx] == 2 {
            self.polarity[idx]
        } else {
            //assert!(self.target_polarity[idx] == 0 || self.target_polarity[idx] == 1);
            self.target_polarity[idx] != 0
        }
    }

    #[requires((@self.polarity).len() > @idx)]
    pub(crate) fn set_polarity(&mut self, idx: usize, polarity: bool) {
        self.polarity[idx] = polarity;
    }
}