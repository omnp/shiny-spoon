import sat
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
            clauses = sat.randomize(clauses)
            variables = set.union(*({abs(e) for e in x} for x in clauses))
            clauses3 = sat.to3(clauses)
            clauses3x = clauses3
            print(len(clauses3x), len(variables))
            t = sat.wrapper(clauses3x, variables)
            print(t)
            print('\r',i, all(any(e in t for e in x) for x in clauses))
    else:
        import dimacs
        filename = sys.argv[1]
        with open(filename) as file:
            text = file.read()
            variables, clauses = dimacs.parse_dimacs(text)
            clauses = {tuple(sorted(c)) for c in clauses}
            #clauses = sat.randomize(clauses)
            print(len(clauses), len(variables))
            print('k', max(len(c) for c in clauses))
            clauses3 = sat.to3(clauses)
            clauses3x = clauses3
            variables_ = set.union(*({abs(e) for e in x} for x in clauses3))
            print(len(clauses3x), len(variables_))
            t = sat.wrapper(clauses3x, variables)
            t = [e for e in t if abs(e) in variables]
            print(t)
            print(all(any(e in t for e in x) for x in clauses))
else:
    """
    Some default examples.
    """
    def generate_instances(n):
        instance = {()}
        yield list(instance)
        instances = [instance]
        v = 1
        i = 0
        for instance in instances:
            if i > n:
                break
            i += 1
            instance_ = list()
            for _,x in enumerate(instance):
                x_ = tuple(sorted(set(x).union({v}),key=abs))
                y_ = tuple(sorted(set(x).union({-v}),key=abs))
                instance_.append(x_)
                instance_.append(y_)
                v += 1
            instances.append(instance_)
            yield instance_
    for instance in generate_instances(9):
        print(instance)
        variables = set()
        if any(instance):
            variables = set.union(*({abs(e) for e in x} for x in instance))
            instance = sat.to3(set(instance))
        print(len(instance), len(variables))
        print(sat.sat(instance, variables, p=False)[0])
    
    for i in range(1,5):
        print('i', i)
        variables = set(range(1,i+1))
        clauses = sat.generate_full_alt(variables, k=i, full=True)
        clauses = list(sat.to3(clauses))
        print(len(clauses), len(variables))
        """
        print('{} instances to check'.format(2**len(clauses)))
        print('\t', end='')
        for k,p in enumerate(sat.partials(range(1,len(clauses)+1))):
            print('\r\t{}'.format(k), end='')
            clauses_ = [x for i,x in enumerate(clauses) if (p[i] > 0)]
            if not sat.sat(clauses_, variables,p=False)[0]:
                print()
                print(p)
                print(clauses_)
        print()
        """
        for i,x in enumerate(clauses):
            clauses_ = set(clauses).difference({x})
            if not sat.sat(clauses_, variables, p=False)[0]:
                clauses = clauses_
        print(clauses)
        print(len(clauses))
    n = int(input("Number of variables: "))
    clauses = sat.generate_assignment(n=n)
    clauses = sat.generate_full_alt(clauses)
    clauses = sat.randomize(clauses)
    variables = set.union(*({abs(e) for e in x} for x in clauses))
    print(len(clauses), len(variables))
    print(sat.wrapper(clauses, variables))
    clauses = {e for e in range(1,10)}
    clauses = sat.generate_full_alt(clauses,k=3)
    variables = set.union(*({abs(e) for e in x} for x in clauses))
    clauses = sat.to3(clauses)
    print(len(clauses), len(variables))
    sat.MaxAll = 0
    t = sat.wrapper(clauses, variables)
    print(t)
    n = len(variables)
    print('MaxAll', sat.MaxAll, n, 2*n + 2*(-1 + n)*n + 4*(-2 + n)*(-1 + n)*n//3)
    _ = input('Press enter...')
    clausesx = set()
    clauses = {(-1,),(-2,),(-3,),}
    clauses = sat.generate_full(clauses)
    clausesx = clausesx.union(clauses)
    clauses = {(-2,),(-3,),(-4,),}
    clauses = sat.generate_full(clauses)
    clausesx = clausesx.union(clauses)
    clauses = {(-1,),(-3,),(-4,),}
    clauses = sat.generate_full(clauses)
    clausesx = clausesx.union(clauses)
    clauses = {(-3,),(-4,),(5,),}
    clauses = sat.generate_full(clauses)
    clausesx = clausesx.union(clauses)
    clauses = {(5,),(6,),(7,),}
    clauses = sat.generate_full(clauses)
    clausesx = clausesx.union(clauses)
    clauses = {(6,),(7,),(8,),}
    clauses = sat.generate_full(clauses)
    clausesx = clausesx.union(clauses)
    clauses = {(8,),(9,),(10,),}
    clauses = sat.generate_full(clauses)
    clausesx = clausesx.union(clauses)
    clauses = {(9,10,),(11,),(12,),}
    clauses = sat.generate_full(clauses)
    clausesx = clausesx.union(clauses)
    clauses = {(-1,),(-2,-3),(-5,-8),}
    clauses = sat.generate_full(clauses)
    clausesx = clausesx.union(clauses)
    clauses = clausesx
    clauses = sat.generate_full(clauses)
    variables = set.union(*({abs(e) for e in x} for x in clauses))
    print(len(clauses), len(variables))
    sat.MaxAll = 0
    for i in range(1024):
        print('Instance', i)
        clauses = sat.randomize(clauses)
        t = sat.sat(clauses, variables)
        print(t[0])
    n = len(variables)
    print('MaxAll', sat.MaxAll, n, 2*n + 2*(-1 + n)*n + 4*(-2 + n)*(-1 + n)*n//3)
    _ = input('Press enter...')
    clauses = sat.generate_assignment(n=n)
    clauses = sat.generate_full_alt(clauses)
    variables = set.union(*({abs(e) for e in x} for x in clauses))
    print(len(clauses), len(variables))
    clauses = sat.randomize(clauses)
    sat.MaxAll = 0
    for i in range(1024):
        print('Instance', i)
        clauses = sat.randomize(clauses)
        t = sat.wrapper(clauses, variables)
        print(t)
    n = len(variables)
    print('MaxAll', sat.MaxAll, n, 2*n + 2*(-1 + n)*n + 4*(-2 + n)*(-1 + n)*n//3)
