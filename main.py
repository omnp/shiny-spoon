import random
import sat
import sys

random.seed(1)
if len(sys.argv) > 1:
    if len(sys.argv) > 2:
        import php
        m,n = sys.argv[1:3]
        m,n = int(m),int(n)
        clauses = php.php(m,n)
        print('PHP:{}x{}'.format(m,n))
        print(len(clauses))
        variables = sat.get_variables(clauses)
        print(len(clauses), len(variables))
        # clauses3 = sat.to3(clauses)
        clauses3 = clauses
        variables = sat.get_variables(clauses3)
        print(len(clauses3), len(variables))
        while True:
            sat.Global_Counter = 0
            clauses3x = sat.randomize(clauses3)
            # clauses3x = clauses3
            try:
                t = sat.sat(clauses3x)
                print(t[0], sat.Global_Counter)
            except ValueError as e:
                print(e)
                exit()
    else:
        import dimacs
        filename = sys.argv[1]
        with open(filename) as file:
            text = file.read()
            variables, clauses = dimacs.parse_dimacs(text)
            clauses = {sat.clause(c) for c in clauses}
            m = len(clauses)
            print(len(clauses), len(variables))
            print('k', max(len(c) for c in clauses))
            clauses3 = clauses
            # clauses3 = sat.to3(clauses)
            clauses3x = clauses3
            variables_ = sat.get_variables(clauses3x)
            print(len(clauses3x), len(variables_))
            sat.Global_Counter = 0
            t = sat.sat(clauses3x)[1]
            if t is not None:
                t = [e for e in t if abs(e) in variables]
                print(t)
                print(all(any(e in t for e in x) for x in clauses))
            else:
                print(t)
            print(sat.Global_Counter)
    exit()

"""
Making an instance and processing it. 
Steps outlined below in the doc string.
"""

variables = set(range(1,7))
xs = sat.generate_full_alt(variables,j=4,k=4,full=True)
variables_ = sat.get_variables(xs)
while len(xs) > 1:
    sat.Global_Counter = 0
    r = tuple(random.choice((1,-1)) * v for v in sorted(variables_))
    xs = {x for x in xs if not all(-e in r for e in x)}
    xs_ = sat.to3(xs)
    print(len(xs_),len(sat.get_variables(xs)))
    print(sat.sat(xs)[0])
    print(sat.Global_Counter)

N = 7
for n in range(1,1+N):
    print(f'Number of variables: {n}')
    variables = set(range(1,1+n))
    m = n#3
    xs = sat.generate_full_alt(variables, j=min(n,m),k=min(n,m),full=True)
    xs_ = set()
    K = 0
    Min = None
    Max = None 
    for i,x in enumerate(xs):
        xs_.add(x)
        sat.Global_Counter = 0
        sat.sat(sat.randomize(set(xs_)))
        K += sat.Global_Counter
        Min = sat.Global_Counter if Min is None else min(Min, sat.Global_Counter)
        Max = sat.Global_Counter if Max is None else max(Max, sat.Global_Counter)
        print(f'\r\t{i}\tSteps taken {sat.Global_Counter} {sat.Global_Counter/len(xs_)}', end='')
    print(f'\nAverage recursive steps taken and minimum and maximum: {K/len(xs)} {Min} {Max}')

import waerden
xs = waerden.waerden(4,5,55)#(3,5,22)
sat.Global_Counter = 0
variables = sat.get_variables(xs)
print(len(xs), len(variables))
print(sat.sat(set(xs))[0], sat.Global_Counter)
