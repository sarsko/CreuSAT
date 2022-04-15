# CreuSAT

## What is this?

A [SAT solver](https://en.wikipedia.org/wiki/SAT_solver) which is written in Rust.
It is formally verified using [Creusot](https://github.com/xldenis/creusot)

## What does that mean?

It means that it solves the [Boolean satisfiability problem](https://en.wikipedia.org/wiki/Boolean_satisfiability_problem) and
that if it states that the formula is satisfiable(SAT), then we **know** that the formula is SAT, and if it states that the formula
is unsatisfiable(UNSAT), then we **know** that the formula is UNSAT.

## Cool. Is it any good?

!TODO

## How do I run it?

It can be built with:
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
where the provided file must be a correctly formatted [DIMACS CNF](https://people.sc.fsu.edu/~jburkardt/data/cnf/cnf.html) file.

## How do I prove the solver?

1. Follow the installation procedure for [Creusot](https://github.com/xldenis/creusot#installing)
2. Clone this repo
3. Run:
```
~/[PATH_TO_CREUSOT]/creusot/mlcfg ~/[PATH_TO_THIS_REPO]/sat/src/lib.rs > ~/[PATH_TO_THIS_REPO]/sat/mlcfgs/lib.mlcfg && ~/[PATH_TO_CREUSOT]/creusot/ide ~/[PATH_TO_THIS_REPO]/sat/mlcfgs/lib.mlcfg
```
4. Prove the solver in the Why3 IDE. It should work to select the lib.mlcfg node and press <kbd>3</kbd>

## Creusot seems really cool! How can I learn it?

!TODO

You could also check out [/naive](/naive/) and [/dpll](/dpll/) for a couple of solvers
which are both easier to grok algorithmically and proof-wise.



## Overview of the repository

Overview of the repository: \
[/src](/src/) - The Rust source code. \
[/dpll](/dpll/) - A fully verified DPLL-based solver. \
[/naive](/naive/) - A fully verified and super naive SAT solver. \
[/cnfs](/cnfs/) - Some example cnf files which are not used in the tests. \
[/tests](/tests/) - Directory for tests. \
[/mlws](/mlws/) - Some WhyML files, among them two verified solvers.
