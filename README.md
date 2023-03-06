# CreuSAT

## What is this?

A [SAT solver](https://en.wikipedia.org/wiki/SAT_solver) which is written in Rust.
It is formally verified using [Creusot](https://github.com/xldenis/creusot).

## What does that mean?

It means that it solves the [Boolean satisfiability problem](https://en.wikipedia.org/wiki/Boolean_satisfiability_problem) (also known as SAT) and
that if it states that the formula is satisfiable (SAT), then we **know** (read: it is proven) that the formula is SAT, and if it states that the formula
is unsatisfiable (UNSAT), then we **know** (read: it is proven) that the formula is UNSAT. Also, the solver is statically proven to be free of runtime panics, which means that it cannot crash.

## Ah, nice. What features does it have?

It currently has the following features:
- Clause analysis with clause learning.
- Unit propagation.
- Two watched literals (2WL) with blocking literals and circular search.
- The variable move-to-front (VMTF) decision heuristic.
- Phase saving.
- Backtracking of the trail to asserting level.
- Exponential moving averages (EMA) based restarts.
- Clause deletion (without garbage collection).

## How do I run it?

Firstly you'll need to [get Rust](https://www.rust-lang.org/tools/install).

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

Remember do add the `--release` as in `cargo test --release [TEST_TO_RUN]`, otherwise it will be built in debug mode, which is *slow*.

## How do I prove the solver?

I would recommend following the instructions in the [Creusot](https://github.com/xldenis/creusot#installing) directory for instructions on how to get Why3 and Creusot up and running.

To prove it you'll need to do the following:
1. Install [Rust](https://www.rust-lang.org/tools/install).
2. Install [Creusot](https://github.com/xldenis/creusot). Clone it, and then run `cargo install --path creusot`.
3. Install Why3. I recommend following the guide in the [Creusot](https://github.com/xldenis/creusot#installing) repository.

CreuSAT is using [Cargo Make](https://github.com/sagiegurari/cargo-make) to make building easier. It can be installed by running:
```
cargo install --force cargo-make
```
After installing Cargo Make, simply run:
```
cargo make prove-CreuSAT
```

And hopefully the Why3 IDE will appear. If not, then most likely something is not installed or pathed correctly, or I have given the wrong instructions (sorry).

If the Why3 IDE appears, then it should work to press <kbd>3</kbd> and wait a bit. If you are doing the proof from scratch, then you will need to wait a while.

The following `cargo make` commands are supported:
- `prove-CreuSAT`/`p` : Generate the MLCFG for `CreuSAT` and run the Why3 IDE.
- `prove-Robinson` : Generate the MLCFG for `Robinson` and run the Why3 IDE.
- `prove-Friday` : Generate the MLCFG for `Friday` and run the Why3 IDE.
- `clean` : Cleans all generated CFG and Why3 session files.
   - `clean-CreuSAT` : Clean just the `CreuSAT` files.
   - `clean-Robinson` : Clean just the `Robinson` files.
   - `clean-Friday` : Clean just the `Friday` files.
- `StarExec` : Generate a `creusat.zip` file ready to be uploaded to the StarExec clusters.
- `StarExec-JigSAT` : Generate a `jigsat.zip` file ready to be uploaded to the StarExec clusters.

## Creusot seems really cool! How can I learn it?

There are a bunch of tests in the Creusot directory which I recommend looking at.

You could also check out [Friday](/Friday/) and [Robinson](/Robinson/) for a couple of verified solvers
which are both easier to grok algorithmically and proof-wise.


## Overview of the repository

Overview of the repository: \
[/CreuSAT](/CreuSAT/) - The source code for CreuSAT. \
[/Friday](/Friday/) - A fully verified and super naive SAT solver. \
[/JigSAT](/JigSAT/) - An unverified solver based on CreuSAT. Used for experimenting. \
[/Robinson](/Robinson/) - A fully verified DPLL-based solver. \
[/mlcfgs](/mlcfgs/) - Output directory for generated mlcfg + Why3 session files. \
[/prelude](/prelude/) - Copy of [prelude](https://github.com/xldenis/creusot/tree/master/prelude) from the Creusot directory. Included here to make `cargo make` happy. \
[/tests](/tests/) - Directory for tests.

## Citing CreuSAT
To cite, you may use the following:

BibLaTeX:
```BibTeX
@thesis{skotam_creusat_2022,
	title = {{CreuSAT}, Using {Rust} and {Creusot} to create the world’s fastest deductively verified {SAT} solver},
	url = {https://www.duo.uio.no/handle/10852/96757},
	institution = {University of Oslo},
	type = {Master's Thesis},
	author = {Skotåm, Sarek Høverstad},
	date = {2022},
}
```
BibTeX:
```BibTeX
@mastersthesis{skotam_creusat_2022,
	title = {{CreuSAT}, Using {Rust} and {Creusot} to create the world’s fastest deductively verified {SAT} solver},
	url = {https://www.duo.uio.no/handle/10852/96757},
	school = {University of Oslo},
	author = {Skotåm, Sarek Høverstad},
	year = {2022},
}
```

