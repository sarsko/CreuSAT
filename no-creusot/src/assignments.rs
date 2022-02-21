use crate::formula::*;
use crate::lit::*;
use crate::trail::*;

// 2 eq unassigned
#[derive(Debug, Eq, PartialEq)]
pub struct Assignments(pub Vec<u8>);

impl Assignments {
    #[inline]
    pub fn set_assignment(&mut self, l: Lit) {
        /*
        if !self.0[l.idx].is_none() {
            panic!("Assignment already set. Attempting to set {:?}", l);
        }
        */
        //assert!(self.0[l.idx].is_none());
        self.0[l.idx] = l.polarity as u8;
    }

    pub fn init_assignments(f: &Formula) -> Assignments {
        //let mut assign: Vec<Option<bool>> = Vec::from_elem(None, f.num_vars);
        //let assign: Vec<Option<bool>> = vec![None; f.num_vars];
        //Assignments(assign)
        Assignments(vec![2; f.num_vars])
    }

    pub fn find_unassigned_lit(&self) -> Option<Lit> {
        let mut i = 0;
        /*
        use rand::Rng;
        let mut rng = rand::thread_rng();
        let b: bool = rng.gen::<f64>() < 0.5;
        */
        while i < self.0.len() {
            let curr = self.0[i];
            if curr == 2 {
                return Some(Lit{ idx: i, polarity: 0 });
            }
            i += 1;
        }
        None
        // Ok wow random gives 7 x slowdown
        // Super simple (and slow) random then linear search
        /*
        use rand::Rng;
        let start = rand::thread_rng().gen_range(0..self.0.len());
        let mut i = start;
        while i < self.0.len() {
            let curr = self.0[i];
            match curr {
                Some(_) => {} // continue
                None => {
                    return Some(Lit{ idx: i, polarity: false });
                }
            }
            i += 1;
        }
        i = 0;
        while i < start {
            let curr = self.0[i];
            match curr {
                Some(_) => {} // continue
                None => {
                    return Some(Lit{ idx: i, polarity: true });
                }
            }
            i += 1;
        }
        None
        */
    }   

    pub fn cancel_until(&mut self, trail: &mut Trail, decisionlevel: usize, level: usize) {
        let mut i: usize = decisionlevel;
        while i > level {
            let decisions = trail.trail.pop().unwrap();
            let mut j: usize = 0;
            while j < decisions.len() {
                let lit = decisions[j];
                //trail.vardata[lit.idx] = (0, Reason::Undefined); // Might as well not wipe it
                self.0[lit.idx] = 2;
                j += 1;
            }
            i -= 1;
        }
    }
}