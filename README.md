# A formally verified sat solver with no name

Overview of the repository: \
[/src](/src/) - The Rust source code. \
[/cnfs](/cnfs/) - Some example cnf files which are not used in the tests.\
[/tests](/tests/) - Directory for tests. Currently tests on 1000 unsat instances
and 1000 sat instances. \
[/mlws](/mlws/) - Some WhyML files, among them two verified solvers.

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

### How to prove the solver

1. Follow the installation procedure for [Creusot](https://github.com/xldenis/creusot#installing)
2. Clone this repo
3. Run:
```
~/[PATH_TO_CREUSOT]/creusot/mlcfg ~/[PATH_TO_THIS_REPO]/sat/src/lib.rs > ~/[PATH_TO_THIS_REPO]/sat/mlcfgs/lib.mlcfg && ~/[PATH_TO_CREUSOT]/creusot/ide ~/[PATH_TO_THIS_REPO]/sat/mlcfgs/lib.mlcfg
```
4. Prove the solver in the Why3 IDE. It should work to select the lib.mlcfg node and press <kbd>3</kbd>

