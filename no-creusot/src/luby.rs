// Pretty much verbatim from Varisat

pub struct Luby {
    u: u64,
    v: u64,
}

impl Default for Luby {
    fn default() -> Luby {
        Luby { u: 1, v: 1 }
    }
}

impl Luby {
    pub fn advance(&mut self) -> u64 {
        let result = self.v;
        if (self.u & self.u.wrapping_neg()) == self.v {
            self.u += 1;
            self.v = 1;
        } else {
            self.v <<= 1;
        }
        result
    }
}
