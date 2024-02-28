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
            sat.J = 0
            sat.I = 0
            print(i, ' ', end='')
            clauses3x = sat.randomize(clauses3)
            #clauses3x = clauses3
            try:
                t = sat.sat(clauses3x)
                #t = sat.sat(clauses3x)
                print(sat.J, sat.I)
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
            sat.J = 0
            sat.I = 0
            t = sat.wrapper(clauses3x)
            t = [e for e in t if abs(e) in variables]
            print(t)
            print(all(any(e in t for e in x) for x in clauses))
            print(sat.J, sat.I)
    exit()

#xs = {(1,2),(-2,-3),(-2,3),(2,-3),(-1,2,3)}
xs = {(1,-2),(-2,-3),(-2,3),(2,-3),(-1,2,3)}
#xs = {(-1, -9), (1, -2, -6), (2, -7), (-4, 6), (2, 5), (-3, -5, 8), (3, 6), (4, 7, 9), (3, -4), (5, -7), (-8, -9), (-1, -8)}
#xs = {(6, 7, 9), (4, -6), (-3, 4), (-7, 8), (1, 8), (-4, -5, -8), (-3, -6), (-2, -9), (5, -9), (-1, 2, 3), (1, -7), (-2, 5)}
sat.J = 0
sat.I = 0
s = sat.sat(xs)
print(*s)
print(sat.J, sat.I)
sat.J = 0
sat.I = 0
print(sat.wrapper(xs))
print(sat.J, sat.I)
exit()
variables = set(range(1,4))
xs = sat.generate_full_alt(variables,j=3,k=3,full=True)
r = tuple(random.choice((1,-1)) * v for v in sorted(variables))
#xs = {x for x in xs if not all(-e in r for e in x)}
xs = sat.to3({x for x in xs if not all(-e in r for e in x)})
variables_ = set.union(*({abs(e) for e in x} for x in xs))
print(len(xs),len(variables_))
print(sat.sat(xs)[0])
clusters = {}
for x in xs:
    k = tuple(abs(e) for e in x)
    if k not in clusters:
        clusters[k] = set()
    clusters[k].add(x)
i = 0
while any(len(v) > 1 for v in clusters.values()):
    i += 1
    for k in clusters:
        if len(clusters[k]) > 1:
            x = random.choice(list(clusters[k]))
            clusters[k].remove(x)
    xs_ = set.union(*clusters.values())
    variables_ = set.union(*({abs(e) for e in x} for x in xs_))
    print(len(xs_),len(variables_))
    xs_ = sat.to3(xs_)
    variables_ = set.union(*({abs(e) for e in x} for x in xs_))
    print(len(xs_),len(variables_))
    print(i, sat.sat(sat.to3(xs_))[0])
