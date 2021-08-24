## A really minimal SAT solver written in Rust

Seems to be working as intended. Thoroughly naïve and slow.

Written to make the initial Creusot proof be as easy as possible.

Currently implements DPLL with linear literal selection. Clones the clauses way too much.

Does not return satisfying assignment.
