use crate::{assignments::*, clause::*, formula::*, lit::*, trail::*};

//#[derive(Debug)]
pub enum Conflict {
    Ground,
    Unit(Clause),
    Learned(usize, Clause),
    Panic,
}

fn idx_in(v: &Vec<Lit>, idx: usize) -> bool {
    let mut i: usize = 0;
    while i < v.len() {
        let lit = &v[i];
        if lit.index() == idx {
            return true;
        }
        i += 1;
    }
    false
}

fn resolve(_f: &Formula, c: &Clause, o: &Clause, idx: usize, _c_idx: usize, _a: &Assignments) -> Clause {
    let mut new: Vec<Lit> = Vec::new();
    let mut i: usize = 0;
    while i < c.rest.len() {
        if c.rest[i].index() == idx {
        } else if idx_in(&new, c.rest[i].index()) {
        } else {
            new.push(c.rest[i]);
        }
        i += 1;
    }
    let mut _o_idx: Option<usize> = None;
    i = 0;
    while i < o.rest.len() {
        /*
        if !idx_in(&new, o.rest[i].idx) && o.rest[i].idx != idx {
            new.push(o.rest[i]);
        }
        */
        if idx_in(&new, o.rest[i].index()) {
        } else if o.rest[i].index() == idx {
            _o_idx = Some(i);
        } else {
            new.push(o.rest[i]);
        }
        i += 1;
    }
    let out = Clause { deleted: false, rest: new };
    out
}


fn choose_literal(c: &Clause, trail: &Trail, i: &mut usize, _f: &Formula) -> Option<usize> {
    while *i > 0 {
        *i -= 1;
        let mut k: usize = 0;
        while k < c.rest.len() {
            if trail.trail[*i].lit.index() == c.rest[k].index() {
                return Some(k);
            }
            k += 1;
        }
    }
    None
}

pub fn analyze_conflict(f: &Formula, trail: &Trail, cref: usize) -> Conflict {
    let decisionlevel = trail.decision_level();
    if decisionlevel == 0 {
        return Conflict::Ground;
    }
    let mut i = trail.trail.len();
    let mut clause = f.clauses[cref].clone();
    let mut s_idx: usize = 0;
    while i > 0 {
        let c_idx = match choose_literal(&clause, trail, &mut i, f) {
            None => return Conflict::Panic,
            Some(b) => b,
        };
        let ante = match &trail.trail[i].reason {
            Reason::Long(c) => &f.clauses[*c],
            o => return Conflict::Panic, // nnTODOnn // This never happens, but is an entirely new proof
        };
        clause = resolve(f, &clause, &ante, trail.trail[i].lit.index(), c_idx, &trail.assignments);
        //resolve_mut(f, &mut clause, &ante, trail.trail[i].lit.idx, c_idx, &trail.assignments);
        s_idx = 0;
        let mut k: usize = 0;
        let mut cnt: usize = 0;
        while k < clause.rest.len() {
            if trail.lit_to_level[clause.rest[k].index()] == decisionlevel {
                cnt += 1;
                if cnt > 1 {
                    break;
                }
                s_idx = k;
            }
            k += 1;
        }
        if cnt == 1 {
            return if clause.rest.len() == 1 { Conflict::Unit(clause) } else { Conflict::Learned(s_idx, clause) };
        }
    }
    return Conflict::Panic; // Okay this is just pure lazyness
}
