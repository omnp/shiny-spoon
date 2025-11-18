# shiny-spoon
3-CNF-SAT (toy) solver

Procedure for checking satisfiability.

The repository name was a GitHub suggestion.

The current implementation and test runners can be found in **resolution.py** (with supporting functions in **sat.py**).
The algorithm used is based on the idea of doing a resolution refutation in reverse: Starting from the empty clause (which is a generator for the whole universe of all possible clauses) generate longer clauses by selecting the next variable by some heuristic strategy and check if any of the original clauses (or any of the clauses already verified to be able to be resolved from the original set of clauses) is a generator for the current target clause. If both the target and target' (where one of its elements is negated in relation to target) are found to be generated from the set of available clauses we can drop that element from the target thus getting a possibly new shorter clause to add to the set of available clauses. Additionally one occasionally cleans the set of available clauses by checking clause-in-clause containments, only keeping the shorter clause. 
