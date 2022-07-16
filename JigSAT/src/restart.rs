pub(crate) enum RestartMode {
    Glucose,
    Luby,
}

struct EMA {
    value: f64,
    alpha: f64,
    beta: f64,
    wait: usize,
    period: usize,
}

impl EMA {
    fn update(&mut self, next: f64) {
        self.value += self.beta * (next - self.value);

        self.wait -= 1;
        if self.beta > self.alpha && self.wait == 0 {
            self.wait = 2 * self.period;
            self.period = 2 * self.period;
            self.beta *= 0.5;
            if self.beta < self.alpha {
                self.beta = self.alpha;
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

impl Default for Glucose {
    fn default() -> Self {
        Glucose {
            minimum_conflicts: 50,
            minimum_conflicts_for_blocking_restarts: 10000,
            ema_lbd_narrow: EMA::new(3e-2),
            ema_lbd_wide: EMA::new(1e-5),
            ema_trail_wide: EMA::new(3e-4),
            last_trail_size: 0,
            force: 1.25,
            block: 1.4,
            num_restarts: 0,
            num_blocked: 0,
        }
    }
}

impl Glucose {
    pub(crate) fn trigger_restart(&mut self, curr_confl: usize) -> bool {
        if curr_confl < self.minimum_conflicts {
            return false;
        }
        if self.ema_lbd_narrow.value / self.ema_lbd_wide.value > self.force {
            self.num_restarts += 1;
            self.minimum_conflicts = curr_confl + 50;
            return true;
        }
        false
    }

    pub(crate) fn update(&mut self, trail_len: usize, lbd: usize) {
        self.ema_trail_wide.update(trail_len as f64);
        self.last_trail_size = trail_len;
        self.ema_lbd_narrow.update(lbd as f64);
        self.ema_lbd_wide.update(lbd as f64);
    }

    pub(crate) fn block_restart(&mut self, curr_confl: usize) -> bool {
        if self.last_trail_size as f64 > self.block as f64 * self.ema_trail_wide.value
            && curr_confl >= self.minimum_conflicts_for_blocking_restarts
        {
            self.minimum_conflicts = curr_confl + 50;
            self.num_blocked += 1;
            return true;
        }
        false
    }
}

struct Luby {
    num_restarts: usize,
    step: usize,
    curr_restarts: usize,
    limit: usize,
}

impl Default for Luby {
    fn default() -> Self {
        Luby { num_restarts: 0, step: 100, curr_restarts: 0, limit: 100 }
    }
}

fn luby(y: f64, mut x: usize) -> usize {
    let mut size = 1;
    let mut seq = 0;
    while size < x + 1 {
        seq += 1;
        size = 2 * size + 1;
    }

    while size - 1 != x {
        size = (size - 1) >> 1;
        seq -= 1;
        x = x % size;
    }
    y.powf(seq as f64) as usize
}

impl Luby {
    pub(crate) fn trigger_restart(&mut self, curr_confl: usize) -> bool {
        if curr_confl <= self.limit {
            return false;
        }

        self.limit = curr_confl + luby(2.0, self.curr_restarts) * self.step;
        self.curr_restarts += 1;
        self.num_restarts += 1;

        true
    }
}

//#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct Restart {
    restart: RestartMode,
    luby: Luby,
    pub(crate) glucose: Glucose,
}

impl Restart {
    pub(crate) fn new() -> Restart {
        Restart { restart: RestartMode::Glucose, luby: Luby::default(), glucose: Glucose::default() }
    }

    pub(crate) fn set_restart_mode(&mut self, mode: RestartMode) {
        self.restart = mode;
    }

    pub(crate) fn swap_mode(&mut self) {
        match self.restart {
            RestartMode::Glucose => self.restart = RestartMode::Luby,
            RestartMode::Luby => self.restart = RestartMode::Glucose,
        }
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
}
