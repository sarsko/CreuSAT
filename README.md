# CreuSAT

## What is this?

A [SAT solver](https://en.wikipedia.org/wiki/SAT_solver) which is written in Rust.
It is formally verified using [Creusot](https://github.com/xldenis/creusot)

## What does that mean?

It means that it solves the [Boolean satisfiability problem](https://en.wikipedia.org/wiki/Boolean_satisfiability_problem)(also known as SAT) and
that if it states that the formula is satisfiable(SAT), then we **know** that the formula is SAT, and if it states that the formula
is unsatisfiable(UNSAT), then we **know** that the formula is UNSAT. Also, the solver is statically proven to be free of runtime panics, which means that it cannot crash.

## Ah, nice. What features does it have?

It currently has the following features:
- Clause analysis with clause learning
- Unit propagation with two watched literals
- The Variable Move To Front(VMTF) decision heuristic
- Phase saving
- Backtracking of the trail to asserting level

## Cool. Is it any good?

!TODO

## Pretty impressive. How do I run it?

Firstly you'll need to [get Rust](https://www.rust-lang.org/tools/install)

Then afterwards, the solver can be built with:
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

To prove it you'll need to have the following installed:
1. [Rust](https://www.rust-lang.org/tools/install)
2. [Why3](todo!) and some SMT-solvers. I recommend:
   - Z3
   - CVC4
   - Alt-Ergo
3. [Creusot](https://github.com/xldenis/creusot#installing)

CreuSAT is using [Cargo Make](https://github.com/sagiegurari/cargo-make) to make building easier. It can be insalled by running:
```
cargo install --force cargo-make
```
After installing Cargo Make, simply run:
```
cargo make prove
```

And hopefully the Why3 IDE will appear. If not, then most likely something is not installed or pathed correctly, or I have given the wrong instructions(sorry).

If the Why3 IDE appears, then it should work to press <kbd>3</kbd> and wait a bit. If you are doing the proof from scratch, then you will need to wait a while.

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
