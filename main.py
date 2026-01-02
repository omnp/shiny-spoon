import random
import sys
import php
import sat
import resolution

random.seed(1)
if len(sys.argv) > 1:
    if len(sys.argv) > 2:
        m, n = sys.argv[1:3]
        m, n = int(m), int(n)
        clauses = php.php(m, n)
        print('PHP:{}x{}'.format(m, n))
        print(len(clauses))
        variables = sat.get_variables(clauses)
        print(len(clauses), len(variables))
    else:
        filename = sys.argv[1]
        with open(filename) as file:
            import dimacs
            text = file.read()
            variables, clauses = dimacs.parse_dimacs(text)
            clauses = {sat.clause(c) for c in clauses}
            m = len(clauses)
            print(len(clauses), len(variables))
            print('k', max(len(c) for c in clauses))
    resolution.counter = 0
    print(resolution.symmetry_breaking(clauses))
    print(resolution.counter)
