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
        #for i in range(512):
        i = 0
        variables = set.union(*({abs(e) for e in x} for x in clauses))
        print(len(clauses), len(variables))
        #clauses3 = sat.to3(clauses)
        clauses3 = clauses
        variables = set.union(*({abs(e) for e in x} for x in clauses3))
        print(len(clauses3), len(variables))
        while True:
            sat.I = 0
            print(i, ' ', end='')
            clauses3x = sat.randomize(clauses3)
            #clauses3x = clauses3
            try:
                t = sat.sat(clauses3x)
                #t = sat.sat(clauses3x)
                print(sat.I)
                if not t[0]:
                    print(t)
                    #print(clauses3x)
                    exit()
            except ValueError:
                print(clauses3x)
                exit()
            exit()
            i += 1
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
            #clauses3 = clauses
            clauses3 = sat.to3(clauses)
            clauses3x = clauses3
            variables_ = set.union(*({abs(e) for e in x} for x in clauses3x))
            print(len(clauses3x), len(variables_))
            #t = sat.sat(clauses3x)[1]
            sat.I = 0
            t = sat.wrapper(clauses3x)
            t = [e for e in t if abs(e) in variables]
            print(t)
            print(all(any(e in t for e in x) for x in clauses))
            print(sat.I)
    exit()

#xs = {(1,2),(-2,-3),(-2,3),(2,-3),(-1,2,3)}
xs = {(1,-2),(-2,-3),(-2,3),(2,-3),(-1,2,3)}
#xs = {(-1, -9), (1, -2, -6), (2, -7), (-4, 6), (2, 5), (-3, -5, 8), (3, 6), (4, 7, 9), (3, -4), (5, -7), (-8, -9), (-1, -8)}
#xs = {(6, 7, 9), (4, -6), (-3, 4), (-7, 8), (1, 8), (-4, -5, -8), (-3, -6), (-2, -9), (5, -9), (-1, 2, 3), (1, -7), (-2, 5)}
xs = {(1,2),(-1,-3),(3,4),(-2,-4)}
xs = {(1,2),(-1,-3),(3,4),(-2,-4),(-1,-4)}
xs = {(1,2),(-1,-3),(3,4),(-2,-4),(-1,-4),(-2,-3)}
sat.I = 0
s = sat.sat(xs)
print(*s)
print(sat.I)
sat.I = 0
print(sat.wrapper(xs))
print(sat.I)
variables = set(range(1,6))
xs = sat.generate_full_alt(variables,j=3,k=4,full=True)
r = tuple(random.choice((1,-1)) * v for v in sorted(variables))
xs = {x for x in xs if not all(-e in r for e in x)}
print(len(xs),len(variables))
sat.I = 0
print(sat.sat(xs)[0])
print(sat.I)
xs = sat.to3({x for x in xs if not all(-e in r for e in x)})
variables_ = set.union(*({abs(e) for e in x} for x in xs))
print(len(xs),len(variables_))
sat.I = 0
print(sat.sat(xs)[0])
print(sat.I)
xs_copy = set(xs)
additional_clauses = sat.generate_full_alt({v for v in variables_.difference(variables)},j=1,k=1,full=True)
xs = xs.union(additional_clauses)
r = r + tuple(random.choice((1,-1)) * v for v in sorted(variables_.difference(variables)))
xs = {x for x in xs if not all(-e in r for e in x)}
print(len(xs),len(variables_))
sat.I = 0
print(sat.sat(xs)[0])
print(sat.I)
sat.I = 0
s = sat.wrapper(xs)
print(s)
print(all(any(e in s for e in x) for x in xs))
print(sat.I)
clusters = {}
for x in additional_clauses:
    k = tuple(abs(e) for e in x)
    if all(e in variables_.difference(variables) for e in k):
        if k not in clusters:
            clusters[k] = set()
        clusters[k].add(x)
xs_additional = set(xs_copy)
for i,k in enumerate(sorted(sorted(clusters),key=len)):
    sat.I = 0
    xs_ = xs_additional.union(clusters[k])
    t = sat.sat(xs_)[0]
    print(i,k,t,sat.I)
    if not t:
        for x in clusters[k]:
            xs_ = xs_additional.union(clusters[k].difference({x}))
            sat.I = 0
            t = sat.sat(xs_)[0]
            print(i,k,t,x,sat.I)
            if t:
                xs_additional = xs_
                break
        else:
            print(i,k,t,None)
            break
    else:
        xs_additional = xs_
print(len(xs_additional.difference(xs_copy)))
