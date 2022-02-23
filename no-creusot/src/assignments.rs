use crate::formula::*;
use crate::lit::*;
use crate::trail::*;
use crate::decision::*;

// 4 is unassigned, 0 is false, 1 is true, 2 is phase saved false and 3 is phase saved true
#[derive(Debug, Eq, PartialEq)]
pub struct Assignments(pub Vec<u8>, usize);

impl Assignments {
    #[inline]
    pub fn set_assignment(&mut self, l: Lit) {
        //assert!(self.0[l.idx].is_none());
        self.0[l.idx] = l.polarity as u8;
    }

    // Seeding with random values seem to be quite a bit better(10-20% speedup)
    pub fn init_assignments(f: &Formula) -> Assignments {
        //let mut assign: Vec<Option<bool>> = Vec::from_elem(None, f.num_vars);
        //let assign: Vec<Option<bool>> = vec![None; f.num_vars];
        //Assignments(assign)
        let mut i = 0;
        use rand::Rng;
        let mut assign = vec![3; f.num_vars];
        let mut rng = rand::thread_rng();
        while i < f.num_vars {
            if rng.gen_bool(0.5) {
                assign[i] = 2
            }
            i += 1;
        }
        Assignments(assign, 0)
    }

    pub fn find_unassigned_lit(&mut self, d: &mut Decisions) -> Option<Lit> {
        return match d.get_next(self) {
            Some(l) => { Some( Lit { idx: l, polarity: self.0[l] == 3 })},
            None => { None }
        }
    }   

    pub fn cancel_until(&mut self, trail: &mut Trail, decisionlevel: usize, level: usize, d: &mut Decisions) {
        let mut i: usize = decisionlevel;
        let mut timestamp = d.linked_list[d.head].ts;
        let mut new_head = d.head;
        while i > level {
            let decisions = trail.trail.pop().unwrap();
            let mut j: usize = 0;
            while j < decisions.len() {
                let lit = decisions[j];
                //trail.vardata[lit.idx] = (0, Reason::Undefined); // Might as well not wipe it
                let curr_timestamp = d.linked_list[lit.idx].ts;
                if  curr_timestamp > timestamp {
                    timestamp = curr_timestamp;
                    new_head = lit.idx;
                }
                self.0[lit.idx] += 2;
                j += 1;
            }
            i -= 1;
        }
        d.head = new_head;
    }
}