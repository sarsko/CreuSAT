type Assignment = Vec<bool>;

struct Lit { var: usize, value: bool }

type Clause = Vec<Lit>;

pub struct Formula { clauses: Vec<Clause>,  num_vars: usize }

struct Pasn { assign: Vec<bool>, ix: usize }

fn complete(pa: &Pasn) -> bool {
    pa.ix == pa.assign.len()
}

fn interp_clause(a: &Assignment, c: &Clause) -> bool {
    let mut i = 0;
    while i < c.len() {
        if a[c[i].var] == c[i].value {
            return true;
        }
        i += 1;
    }
    false
}

fn interp_formula(a: &Assignment, f: &Formula) -> bool {
    let mut i = 0;
    while i < f.clauses.len() {
        if !interp_clause(a, &f.clauses[i]) {
            return false;
        }
        i += 1;
    }
    true
}

fn set_true(pa: &Pasn) -> Pasn {
    let mut new_assign = pa.assign.clone();
    new_assign[pa.ix] = true;
    Pasn { assign: new_assign, ix: pa.ix + 1 }
}

fn set_false(pa: &Pasn) -> Pasn {
    let mut new_assign = pa.assign.clone();
    new_assign[pa.ix] = false;
    Pasn { assign: new_assign, ix: pa.ix + 1 }
}

fn inner(f: &Formula, pa: Pasn) -> bool {
    if complete(&pa) {
        return interp_formula(&pa.assign, f);
    } else {
        if inner(f, set_true(&pa)) {
            return true;
        } else {
            return inner(f, set_false(&pa));
        }
    }
    true
}

pub fn solver(f: &Formula) -> bool {
    let base = Pasn { assign: vec![false; f.num_vars], ix: 0 };
    inner(f, base)
}
