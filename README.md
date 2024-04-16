# shiny-spoon
3-CNF-SAT (toy) solver

Recursive procedure for checking satisfiability.

Now will require the **SymPy** Python package installed (pip install --user sympy). SymPy is used for a *driver* function which aims to limit the number the satisfying assignments by auxiliary clauses hoping to make the main solving procedure run faster. Yet to be tested if that is in fact the case on any instances.

The repository name was a GitHub suggestion.

There might be an upcoming Rust version (of parts of this repo) which will be called, naturally, rusty-spoon. That name I figured out myself.
Just to brush up on Rust a little bit.
