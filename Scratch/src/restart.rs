extern crate creusot_contracts;
use creusot_contracts::invariant::{Invariant, self};
use creusot_contracts::{*, pearlite, ensures, requires, predicate, trusted};

pub(crate) enum RestartMode {
    Glucose,
    Luby,
}

#[allow(clippy::upper_case_acronyms)]
struct EMA {
    value: f64,
    alpha: f64,
    beta: f64,
    wait: usize,
    period: usize,
}

impl Invariant for EMA {
    #[why3::attr = "inline:trivial"]
    #[predicate]
    fn invariant(self) -> bool {
        pearlite! {
            self.wait > 0usize
            && self.period > 0usize
        }
    }
}

impl EMA {
    fn update(&mut self, next: f64) {
        self.value += self.beta * (next - self.value);

        if self.beta > self.alpha {
            self.wait -= 1;
            if self.wait == 0 {
                if self.period < usize::MAX / 2 {
                    self.period *= 2;
                }
                self.wait = self.period;
                self.beta *= 0.5;
                if self.beta < self.alpha {
                    self.beta = self.alpha;
                }
            }
        }
    }

    fn new(alpha: f64) -> Self {
        EMA { value: 1.0, alpha, beta: 1.0, wait: 1, period: 1 }
    }
}
pub(crate) struct Glucose {
    minimum_conflicts: usize,
    minimum_conflicts_for_blocking_restarts: usize,
    ema_lbd_narrow: EMA,
    ema_lbd_wide: EMA,
    ema_trail_wide: EMA,
    last_trail_size: usize,
    force: f64,
    block: f64,
    num_restarts: usize,
    num_blocked: usize,
}

impl Invariant for Glucose {
    #[why3::attr = "inline:trivial"]
    #[predicate]
    fn invariant(self) -> bool {
        self.ema_lbd_narrow.invariant()
        && self.ema_lbd_wide.invariant()
        && self.ema_trail_wide.invariant()
    }
}

fn div_float_with_ten_n_times(mut f: f64, n: usize) -> f64 {
    for _ in 0..n {
        f /= 10.0;
    }
    f
}

// TODO: This should be Default, but default seems to be broken under Creusot.
impl Glucose {
    fn new() -> Self {
        Glucose {
            minimum_conflicts: 50,
            minimum_conflicts_for_blocking_restarts: 10_000,
            ema_lbd_narrow: EMA::new(3e-2), // 0.03
            ema_lbd_wide: EMA::new(div_float_with_ten_n_times(1e-3, 2)),//EMA::new(1e-5), // 0.00001
            ema_trail_wide: EMA::new(3e-4), // 0.0003
            last_trail_size: 0,
            force: 1.25,
            block: 1.4,
            num_restarts: 0,
            num_blocked: 0,
        }
    }
}

// TODO: This is a temporary measure since casts currently don't work
#[trusted]
fn usize_to_f64(u: usize) -> f64 {
    u as f64
}

// TODO: This is a temporary measure since casts currently don't work
#[trusted]
fn f64_to_usize(f: f64) -> usize {
    f as usize
}

fn powf(f: f64, u: usize) -> f64 {
    let mut o = 1.0;
    for _ in 0..u {
        o *= f;
    }
    o
}

impl Glucose {
    pub(crate) fn trigger_restart(&mut self, curr_confl: usize) -> bool {
        if curr_confl < self.minimum_conflicts {
            return false;
        }
        if self.ema_lbd_narrow.value / self.ema_lbd_wide.value > self.force {
            if self.num_restarts < usize::MAX {
                self.num_restarts += 1;
            }
            if curr_confl < usize::MAX - 50 {
                self.minimum_conflicts = curr_confl + 50;
            }
            return true;
        }
        false
    }

    pub(crate) fn update(&mut self, trail_len: usize, lbd: usize) {
        self.ema_trail_wide.update(usize_to_f64(trail_len));
        self.last_trail_size = trail_len;
        self.ema_lbd_narrow.update(usize_to_f64(lbd));
        self.ema_lbd_wide.update(usize_to_f64(lbd));
    }

    pub(crate) fn block_restart(&mut self, curr_confl: usize) -> bool {
        if usize_to_f64(self.last_trail_size) > self.block * self.ema_trail_wide.value
            && curr_confl >= self.minimum_conflicts_for_blocking_restarts
        {
            if curr_confl < usize::MAX - 50 {
                self.minimum_conflicts = curr_confl + 50;
            }
            if self.num_blocked < usize::MAX {
                self.num_blocked += 1;
            }
            return true;
        }
        false
    }
}


// TODO: I think this can be implemented in an easier way (proof wise). I don't remember if I had a Luby-scheme in CreuSAT back in the day.
struct Luby {
    //num_restarts: usize, // TODO: Do I need this for anything ?
    step: usize,
    curr_restarts: usize,
    limit: usize,
}

impl Invariant for Luby {
    #[why3::attr = "inline:trivial"]
    #[predicate]
    fn invariant(self) -> bool {
        self.step > 0usize
    }
}

impl Luby {
    // TODO: This should be Default, but default seems to be broken under Creusot.
    fn new() -> Self {
        Luby { /*num_restarts: 0,*/ step: 100, curr_restarts: 0, limit: 100 }
    }
}


#[requires(x@ < 9223372036854775806)] // (usize::MAX - 2) / 2
fn luby(y: f64, x: usize) -> usize {
    let mut size = 1;
    let mut seq: usize = 0;
    #[invariant(size@ <= usize::MAX@)]
    #[invariant(size@ > 0)]
    #[invariant(seq@ < size@)]
    while size < x + 1 {
        seq += 1;
        size = 2 * size + 1;
    }

    // TODO: This loop became ugly with a bunch of checks
    let mut x = x;
    while size > 0 && seq > 0 && size - 1 != x {
        // TODO: shr not supported
        //size = (size - 1) >> 1;
        size = (size - 1) / 2;
        seq -= 1;
        if size > 0 {
            x %= size;
        }
    }
    // TODO: powf etc don't have specs
    //f64_to_usize(y.powf(usize_to_f64(seq)))
    f64_to_usize(powf(y, seq))
}

impl Luby {
    // TODO: This stuff is _ugly_ look into simplifying
    pub(crate) fn trigger_restart(&mut self, curr_confl: usize) -> bool {
        if curr_confl <= self.limit {
            return false;
        }

        // This is a purely pro-forma check. 
        if self.curr_restarts >= 9223372036854775806 { // (usize::MAX - 2) / 2
            return true;
        }

        let mut incr = luby(2.0, self.curr_restarts); 
        if incr < usize::MAX / self.step  {
            incr *= self.step
        }
        if usize::MAX - curr_confl > incr {
            self.limit = curr_confl + incr;
        }
        self.curr_restarts += 1;
        //self.num_restarts += 1;

        true
    }
}

//#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct Restart {
    restart: RestartMode,
    luby: Luby,
    pub(crate) glucose: Glucose,
}

impl Invariant for Restart {
    #[predicate]
    fn invariant(self) -> bool {
        pearlite! {
            self.luby.invariant()
            && self.glucose.invariant()
        }
    }
}

impl Restart {
    pub(crate) fn new() -> Restart {
        Restart { restart: RestartMode::Glucose, luby: Luby::new(), glucose: Glucose::new() }
    }

    pub(crate) fn set_restart_mode(&mut self, mode: RestartMode) {
        self.restart = mode;
    }

    pub(crate) fn trigger_restart(&mut self, curr_confl: usize) -> bool {
        match self.restart {
            RestartMode::Glucose => self.glucose.trigger_restart(curr_confl),
            RestartMode::Luby => self.luby.trigger_restart(curr_confl),
        }
    }

    pub(crate) fn block_restart(&mut self, curr_confl: usize) -> bool {
        match self.restart {
            RestartMode::Glucose => self.glucose.block_restart(curr_confl),
            RestartMode::Luby => true,
        }
    }

    pub(crate) fn get_number_of_restarts(&self) -> usize {
        if usize::MAX - self.glucose.num_restarts > self.luby.curr_restarts {
            self.glucose.num_restarts + self.luby.curr_restarts
        } else {
            usize::MAX
        }
    }
}