


#[derive(Debug, Default)]
pub struct Stats {
    pub nb_glues: usize,
    pub nb_bin: usize,
    pub nb_un: usize,
    pub lcm_tested: usize,
    pub lcm_reduced: usize,
    pub nb_walk: usize,
    pub walk_time: usize,
    pub nb_flips: usize,
    pub no_decision_conflict: usize,
    pub nb_reduced_clauses: usize,
    pub nb_self_subsumptions: usize,
    pub nb_stats: usize,
}