# shiny-spoon
3-CNF-SAT (toy) solver

Used to use a ~~recursive~~ procedure now uses an iterative version of the same to try and find a satisfying assignment.
The algorithm is a hybrid of the most naive recursion (originally, now iterative) combined with checking target clause generation (whether the empty clause can be generated from the original clause set) somewhat accelerated by a sort of version of unit clause propagation. The hybrid uses less or equal recursion steps than the naive recursion alone for what it's worth.

Now will require the **SymPy** Python package installed (pip install --user sympy). SymPy is used for a *driver* function

The repository name was a GitHub suggestion.

There might be an upcoming Rust version (of parts of this repo) which will be called, naturally, rusty-spoon. That name I figured out myself.
Just to brush up on Rust a little bit.
