import random
import sat
import sys
sys.setrecursionlimit(1000000)
random.seed(1)
if len(sys.argv) > 1:
    if len(sys.argv) > 2:
        import php
        m,n = sys.argv[1:3]
        m,n = int(m),int(n)
        clauses = php.php(m,n)
        print('PHP:{}x{}'.format(m,n))
        print(len(clauses))
        for i in range(512):
            clauses = sat.randomize(clauses)
            variables = set.union(*({abs(e) for e in x} for x in clauses))
            print(len(clauses), len(variables))
            clauses3 = sat.to3(clauses)
            clauses3x = sat.randomize(clauses3)
            variables = set.union(*({abs(e) for e in x} for x in clauses3x))
            print(len(clauses3x), len(variables))
            t = sat.sat(clauses3x)#wrapper(clauses3x, variables, K=3)
            print(t)
    else:
        import dimacs
        filename = sys.argv[1]
        with open(filename) as file:
            text = file.read()
            variables, clauses = dimacs.parse_dimacs(text)
            clauses = {tuple(sorted(c)) for c in clauses}
            m = len(clauses)
            print(len(clauses), len(variables))
            print('k', max(len(c) for c in clauses))
            clauses3 = sat.to3(clauses)
            clauses3x = clauses3
            variables_ = set.union(*({abs(e) for e in x} for x in clauses3x))
            print(len(clauses3x), len(variables_))
            t = sat.wrapper(clauses3x, variables)
            t = [e for e in t if abs(e) in variables]
            print(t)
            print(all(any(e in t for e in x) for x in clauses))
    exit()

xs = {(1,2),(-2,-3),(-2,3),(2,-3),(-1,2,3)}
print(sat.sat(xs))
variables = set(range(1,12))
xs = sat.generate_full_alt(variables,j=3,k=4,full=True)
r = tuple(random.choice((1,-1)) * v for v in sorted(variables))
xs = sat.to3({x for x in xs if not all(-e in r for e in x)})
variables_ = set.union(*({abs(e) for e in x} for x in xs))
xs = sat.randomize(xs)
print(sat.sat(xs))
