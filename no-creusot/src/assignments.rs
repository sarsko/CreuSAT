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
        Assignments(vec![4; f.num_vars], 0)
    }

    pub fn find_unassigned_lit(&mut self, d: &mut Decisions) -> Option<Lit> {
        match d.get_next(self) {
            Some(l) => {
                return Some(Lit { idx: l, polarity: true }); // TODO swap to b
            },
            None => {
                return None;
            }
        }
        /*
        let mut i = d.head;
        while i < d.lit_order.len() {
            let curr = self.0[d.lit_order[i]];
            if curr >= 2 {
                let b = curr != 2;
                d.head = i;
                return Some(Lit{ idx: d.lit_order[i], polarity: b });
            }
            i += 1;
        }
        i = 0;
        while i < d.head {
            let curr = self.0[d.lit_order[i]];
            if curr >= 2 {
                let b = curr != 2;
                d.head = i;
                return Some(Lit{ idx: d.lit_order[i], polarity: b });
            }
            i += 1;
        }
        return None
        */
        /*
        let mut i = self.1;
        //let mut i = 0;
        while i < d.lit_order.len() {
            //let curr = self.0[i];
            let curr = self.0[d.lit_order[i]];
            println!("{}", i);
            if curr >= 2 {
                /*
                let b = if curr == 4 {
                    use rand::Rng;
                    let mut rng = rand::thread_rng();
                    rng.gen::<f64>() < 0.5
                } else { curr != 2 };
                */
                let b = curr != 2;
                // 3 -> 1 and 2 -> 0
                self.1 = i + 1;
                //self.1 = 0;
                //return Some(Lit{ idx: d.lit_order[i], polarity: b });
                return Some(Lit{ idx: d.lit_order[i], polarity: b });
                return Some(Lit{ idx: i, polarity: b });
            }
            i += 1;
        }
        None
        */
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

    // Surprised that this isnt faster
    pub fn cancel_long(&mut self, trail: &mut Trail) {
        let mut i: usize = trail.trail.len();
        //let mut minseen = self.1;
        while i > 1 {
            let decisions = trail.trail.pop().unwrap();
            let mut j: usize = 0;
            while j < decisions.len() {
                let lit = decisions[j];
                //trail.vardata[lit.idx] = (0, Reason::Undefined); // Might as well not wipe it
                //if lit.idx < minseen {
                //    minseen = lit.idx;
                //}
                self.0[lit.idx] += 2;
                j += 1;
            }
            i -= 1;
        }
        self.1 = 0;
        //self.1 = minseen;
    }

    pub fn cancel_until(&mut self, trail: &mut Trail, decisionlevel: usize, level: usize, d: &mut Decisions) {
        let mut i: usize = decisionlevel;
        //let mut minseen = self.1;
        let mut min_timestamp = d.linked_list[d.head].ts;
        let mut new_head = d.head;
        while i > level {
            let decisions = trail.trail.pop().unwrap();
            let mut j: usize = 0;
            while j < decisions.len() {
                let lit = decisions[j];
                //trail.vardata[lit.idx] = (0, Reason::Undefined); // Might as well not wipe it
                let curr_timestamp = d.linked_list[lit.idx].ts;
                if  curr_timestamp > min_timestamp {
                    min_timestamp = curr_timestamp;
                    new_head = lit.idx;
                }
                self.0[lit.idx] += 2;
                j += 1;
            }
            i -= 1;
        }
        //self.1 = 0;
        d.head = new_head;
        //d.head = 0;
        //self.1 = minseen;
    }
}