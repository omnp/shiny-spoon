from sat import *
import sys
if len(sys.argv) > 1:
    if len(sys.argv) > 2:
        import php
        m,n = sys.argv[1:3]
        m,n = int(m),int(n)
        clauses = php.php(m,n)
        print('PHP:{}x{}'.format(m,n))
        print(len(clauses))
        for i in range(512):
            clauses = randomize(clauses)
            variables = set.union(*({abs(e) for e in x} for x in clauses))
            clauses3 = to3(clauses)
            clauses3x = clauses3
            print(len(clauses3x), len(variables))
            t = wrapper(clauses3x, variables)
            print(t)
            print('\r',i, all(any(e in t for e in x) for x in clauses))
    else:
        import dimacs
        filename = sys.argv[1]
        with open(filename) as file:
            text = file.read()
            variables, clauses = dimacs.parse_dimacs(text)
            clauses = {tuple(sorted(c)) for c in clauses}
            #clauses = randomize(clauses)
            print(len(clauses), len(variables))
            print('k', max(len(c) for c in clauses))
            clauses3 = to3(clauses)
            clauses3x = clauses3
            variables_ = set.union(*({abs(e) for e in x} for x in clauses3))
            print(len(clauses3x), len(variables_))
            t = wrapper(clauses3x, variables)
            t = [e for e in t if abs(e) in variables]
            print(t)
            print(all(any(e in t for e in x) for x in clauses))
else:
    """
    Some default examples.
    """
    n = int(input("Number of variables: "))
    clauses = generate_assignment(n=n)
    clauses = generate_full_alt(clauses)
    clauses = randomize(clauses)
    variables = set.union(*({abs(e) for e in x} for x in clauses))
    print(len(clauses), len(variables))
    print(wrapper(clauses, variables))
    clauses = {e for e in range(1,10)}
    clauses = generate_full_alt(clauses,k=3)
    variables = set.union(*({abs(e) for e in x} for x in clauses))
    clauses = to3(clauses)
    print(len(clauses), len(variables))
    MaxAll = 0
    t = wrapper(clauses, variables)
    print(t)
    n = len(variables)
    print('MaxAll', MaxAll, n, 2*n + 2*(-1 + n)*n + 4*(-2 + n)*(-1 + n)*n//3)
    _ = input('Press enter...')
    clausesx = set()
    clauses = {(-1,),(-2,),(-3,),}
    clauses = generate_full(clauses)
    clausesx = clausesx.union(clauses)
    clauses = {(-2,),(-3,),(-4,),}
    clauses = generate_full(clauses)
    clausesx = clausesx.union(clauses)
    clauses = {(-1,),(-3,),(-4,),}
    clauses = generate_full(clauses)
    clausesx = clausesx.union(clauses)
    clauses = {(-3,),(-4,),(5,),}
    clauses = generate_full(clauses)
    clausesx = clausesx.union(clauses)
    clauses = {(5,),(6,),(7,),}
    clauses = generate_full(clauses)
    clausesx = clausesx.union(clauses)
    clauses = {(6,),(7,),(8,),}
    clauses = generate_full(clauses)
    clausesx = clausesx.union(clauses)
    clauses = {(8,),(9,),(10,),}
    clauses = generate_full(clauses)
    clausesx = clausesx.union(clauses)
    clauses = {(9,10,),(11,),(12,),}
    clauses = generate_full(clauses)
    clausesx = clausesx.union(clauses)
    clauses = {(-1,),(-2,-3),(-5,-8),}
    clauses = generate_full(clauses)
    clausesx = clausesx.union(clauses)
    clauses = clausesx
    clauses = generate_full(clauses)
    variables = set.union(*({abs(e) for e in x} for x in clauses))
    print(len(clauses), len(variables))
    MaxAll = 0
    for i in range(1024):
        print('Instance', i)
        clauses = randomize(clauses)
        t = sat(clauses, variables)
        print(t[0])
    n = len(variables)
    print('MaxAll', MaxAll, n, 2*n + 2*(-1 + n)*n + 4*(-2 + n)*(-1 + n)*n//3)
    _ = input('Press enter...')
    clauses = generate_assignment(n=n)
    clauses = generate_full_alt(clauses)
    variables = set.union(*({abs(e) for e in x} for x in clauses))
    print(len(clauses), len(variables))
    clauses = randomize(clauses)
    MaxAll = 0
    for i in range(1024):
        print('Instance', i)
        clauses = randomize(clauses)
        t = wrapper(clauses, variables)
        print(t)
    n = len(variables)
    print('MaxAll', MaxAll, n, 2*n + 2*(-1 + n)*n + 4*(-2 + n)*(-1 + n)*n//3)