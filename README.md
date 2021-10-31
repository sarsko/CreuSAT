# A formally verified sat solver with no name

Overview of the repository: \
[/src](/src/) - The Rust source code. \
[/cnfs](/cnfs/) - Some example cnf files which are not used in the tests.\
[/tests](/tests/) - Directory for tests. Currently tests on 1000 unsat instances
and 1000 sat instances. \
[/mlws](/mlws/) - Formally verified(and naïve) WhyML solver which
[solver_mirror.rs](/src/solver_mirror.rs) is based on.

### Current status

[solver_mirror.rs](/src/solver_mirror.rs) is verified to be correct. \
Work was started on [solver_dpll.rs](/src/solver_dpll.rs), but this work was
abandoned when I realized the approach was flawed. This led to
[solver_dpll_noproofs.rs](/src/solver_dpll_noproofs.rs), which is proven safe,
and is currectly in the process of being proven correct - see:
[solver_dpll_withproofs.rs](/src/solver_dpll_withproofs.rs) and
[formula_state.rs](/src/formula_state.rs)


### How to run

The unverified solver can be built with:
```
cargo build
```
and tested with:
```
cargo test
```
and run with
```
cargo run -- --file [PATH_TO_FILE]
```
where the provided file must be a correctly formatted CNF.
Error checking is minimal and the parser may panic.

Running the verified versions is currently not supported, as pass-through
compilation has to be implemented in Creusot first.

For instructions on how to prove the verified solvers, see
the [Creusot](https://github.com/xldenis/creusot) repository
