import random

def partials(x,full=False):
    """
    x is a set of literals
    This function generates all the combinations of positive and negative literals in 
    the given variables.
    full=True means generate all
    full=False means generate all except for the one where each element of x is negated
    """
    for i in range(2**len(x)-(1 if not full else 0)):
        z = list(x)
        j = 0
        while i:
            if i & 1:
                z[j] = -z[j]
            i >>= 1
            j += 1
        yield tuple(sorted(z,key=abs))

J = 0
I = 0
def sat(xs):
    if not xs:
        return True, set()
    if not all(xs):
        return False, None
    I = 0
    def resolve(xs):
        xs_ = list(sorted(xs,key=lambda x:tuple(abs(e) for e in x)))
        result = set(xs)
        res = set()
        counter = 100
        while True:
            n = len(result)
            y = None
            for x in xs_:
                if y is None:
                    y = x
                else:    
                     if sum(1 if -e in y else 0 for e in x) == 1:
                        z = set(x).difference({-e for e in y}).union(set(y).difference({-e for e in x}))
                        z = tuple(sorted(z,key=abs))
                        if not any(all(e in z for e in x) for x in result):
                            if any(sum(1 if -e in z else 0 for e in x) == 1 for x in result):
                                y = z
                                counter = 100
            if y not in xs:
                if len(y) <= 3:
                    result.add(y)
                    res.add(y)
                    print(len(result), y)
            for x in list(result):
                for y in result:
                    if x != y and all(e in x for e in y):
                        result.remove(x)
                        break
            for x in list(xs_):
                for y in result:
                    if x != y and all(e in x for e in y):
                        xs_.remove(x)
                        break
            if n == len(result) and counter == 0:
                break
            counter -= 1
            random.shuffle(xs_)
        return result
    Resolvers = {}
    _xs_ = set(xs)  
    i = 0
    Depth = 0
    RESOLVE = set()
    def resolve(xs, target, targets = set(), depth=0):
        """
            Recursive procedure for checking unsatisfiability. Whether target can be resolved from the given clauses.
        """
        global I
        nonlocal Resolvers
        nonlocal Depth
        nonlocal _xs_
        nonlocal RESOLVE
        depth += 1
        I += 1
        Depth = max(Depth, depth)
        print('depth',depth)
        if target in _xs_ or any(all(e in target for e in x) for x in _xs_):
            print('target (in orig. set)', target)
            return {target}
        else:
            if target in Resolvers or any(all(e in target for e in x) for x in Resolvers):
                print('target (in Resolvers, 0)', target)
                return {target}
            print('target', target)
            #xs_ = list(sorted(sorted(xs,key=len),key=lambda x:tuple(abs(e) for e in x)))
            xs_ = list(sorted(sorted(xs,key=lambda x:tuple(abs(e) for e in x)),key=len))
            for x in list(xs_):
                for y in set(Resolvers).union(xs_):
                    if x != y and all(e in x for e in y):
                        xs_.remove(x)
                        break
            D = set()
            ##X = None
            ##X_tx = None
            ##X_d = None
            for x in xs_:
                if not any(-e in x for e in target) and (not target or any(e in x for e in target)):
                    D.add(x)
                    d = set(x).difference(set(target))
                    tx = set(target).difference(set(x))
                    #if X is None or len(tx) < len(X_tx):
                    ##if X is None or len(d) < len(X_d):
                    ##    X = x
                    ##    X_tx = tx
                    ##    X_d = d
            ##if X is not None:
                    ##x = X
                    ##tx = X_tx
                    ##d = X_d
                    ##D = D.union({x}).union(Resolvers)
                    a = b = c = e = None
                    if not d:
                        if target not in Resolvers:
                            Resolvers[target] = {(x,x)}
                    while d:
                        e = max(d,key=abs)
                        d.remove(e)
                        a = tuple(sorted({-e}.union(tx),key=abs))#(-e,)
                        b = tuple(sorted(set(x).difference({e}).union({-e}).union(tx),key=abs))
                        c = tuple(sorted(set(x).difference({e}).union(tx),key=abs))
                        #print(e,d,a,b,c,'t',target)
                        u,v = None,None
                        #if a not in targets:
                        #    v = resolve(xs.difference(x), a, targets.union({a,b}), depth)
                        if b not in targets:
                            #u = resolve(xs.difference(x), b, targets.union({a,b}), depth)
                            ##for h in Resolvers:
                            ##    if all(f in b for f in h):
                            ##        Resolvers[c] = Resolvers[h]
                            ##        u = set()
                            ##        break
                            ##else:
                                #u = resolve(xs.difference(x), b, targets.union({b}), depth)
                                u = resolve(set(xs_).difference(D), b, targets.union({b}), depth)
                        if u is None and v is None:
                            break
                        #RESOLVE.add(c)
                        if c not in Resolvers:
                            Resolvers[c] = set()
                        if u is not None:
                            Resolvers[c].add(tuple(sorted([x,b],key=lambda x:tuple(abs(e) for e in x))))
                        #if v is not None:
                        #    Resolvers[c].add(tuple(sorted([x,a],key=lambda x:tuple(abs(e) for e in x))))
                        x = c
                        d = set(x).difference(set(target))
                        if x == target:
                            assert(target in Resolvers)
                            print('target (in Resolvers, 1)', target, Resolvers[target])                
                            return {target}
                        #break
                    else:
                        ##print(e,d,a,b,c,'t',target)
                        assert(target in Resolvers)
                        #if target in Resolvers:
                        print('target (in Resolvers, 2)', target, Resolvers[target])                
                        return {target}
                    #break
    target = ()
    Depth = 0
    r = resolve(xs, target, {target})
    print(r, Depth)
    print(len(xs))
    #print(len(RESOLVE))
    return not(r is not None and () in r), r

    target = ()
    Depth = 0
    def resolvers(target, depth = 0):
        nonlocal Resolvers
        nonlocal Depth
        depth += 1
        if target in _xs_:
            Depth = max(Depth, depth)
            print('target (in orig. set)', target)
            return {target}
        else:
            print('target', target)
            for x,y in Resolvers[target]:
                print('x y', x, y)
                return resolvers(x,depth).union(resolvers(y,depth))
    r = resolvers(target)
    print(r)
    print(r == _xs_)
    print(Depth)

    def rec(a = set(), T_=None):
        nonlocal xs, I
        I += 1
        xs_ = {tuple(e for e in x if -e not in a) for x in xs if not any(e in a for e in x)}
        while True:
            xs_ = {tuple(e for e in x if -e not in a) for x in xs_ if not any(e in a for e in x)}
            if not xs_:
                return True, a
            if not all(xs_):
                return False, None
            literals = set.union(*({e for e in x} for x in xs_))
            notneg = [v for v in literals if -v not in literals or (v,) in xs_]
            a = a.union(set(notneg))
            if any(-f in a for f in a):
                return False, None
            if not notneg:
                break
        xs__ = set(xs_)
        for x in reversed(sorted(reversed(sorted(xs_,key=lambda x:tuple(abs(e) for e in x))),key=lambda x:sum(sum(1 if -e in y or e in y else 0 for e in x) for y in xs_))):
            T = {}
            for e in x:
                if e not in T:
                    T[e] = {y for y in xs__ if e not in y}
                    xs__ = xs__.difference(T[e])
                    T[e] = {tuple(f for f in y if f != -e) for y in T[e] if -e in y}
            for e in sorted(T,key=abs):
                if e not in a:
                    t = {e}
                    for y in T[e]:
                        if len(y) <= 1:
                            if len(y) < 1:
                                t.add(-e)
                            t = t.union(set(y))
                    t_ = a.union({e}).union(t)
                    if not any(-f in t_ for f in t_):
                        t_ = rec(a.union({e}).union(t_))[1]
                        if t_ is not None:
                            if not any(-e in t_ for e in t_):
                                a = a.union(t_)
                                break
            break
        if not any(-e in a for e in a):
            if all(any(e in a for e in x) for x in xs_):
                return True, a
        #print('Returning False')
        return False, None
    r = rec()
    print('steps', I)
    return r    

def wrapper(xs):
    """
    Tries to generate a valid assignment, given one exists.
    """
    xs = {tuple(sorted(x,key=abs)) for x in xs}
    clauses = set(xs)
    variables = list(sorted(set.union(*(set(abs(e) for e in x) for x in clauses))))
    t = sat(clauses)
    if t[0]:
        result = set()
        for v in variables:
            for u in [v,-v]:
                print('v',u)
                cs = {tuple(e for e in x if e != -u) for x in clauses if u not in x}
                t = sat(cs)
                if t[0]:
                    clauses = cs
                    result.add(u)
                    break
            else:
                print(clauses)
                print(v)
                raise ValueError
        return result
    return set()

def tok(cl,r=3):
    """
    cl is a set of clauses
    r >= 3
    This function generates a set of clauses where the length of each clause is at most r.
    """
    if not cl:
        return set()
    vs = set.union(*(set(abs(e) for e in x) for x in cl))
    i = max(vs) + 1
    cll = {x for x in cl if len(x) <= r}
    cl = cl.difference(cll)
    cln = set()
    for c in cl:
        c = tuple(sorted(c,key=abs))
        while len(c) > r:
            c0 = tuple(sorted(c[:r-1] + (i,),key=abs))
            c = tuple(sorted(c[r-1:] + (-i,),key=abs)) 
            i += 1
            cln.add(c0)
        cln.add(c)
    assert(all(len(x) <= r for x in cln))
    cll = cll.union(cln)
    return cll

to3 = lambda cl: tok(cl,r=3)

def generate_assignment(n):
    """
    n = number of variables
    Generates a random assignment (a set of literals).
    """
    r = list(range(1,n+1))
    for i,e in enumerate(r):
        if random.choice((True,False)):
            r[i] = -e
    return set(r)

def generate_assignment_from_set(vs):
    """
    vs = variables
    Generates a random assignment (a set of literals).
    """
    r = list(vs)
    for i,e in enumerate(r):
        if random.choice((True,False)):
            r[i] = -e
    return set(r)

def generate_full(xs, j=2, k=3, exact=True, full=True):
    """
    xs is the set of clauses defining the solutions
    Generates a set of clauses containing the given clauses as a solution (which may be empty).
    """
    vs = set.union(*({abs(e) for e in x} for x in xs))
    xs = list(xs)
    for x in xs:
        if len(x) < k:
            for v in vs:
                for e in [v,-v]:
                    if e not in x and -e not in x:
                        y = set(x).union({e})
                        y = tuple(sorted(y,key=abs))
                        if y not in xs:
                            if full or len({z for z in xs if {abs(f) for f in z} == {abs(f) for f in y}}) < 2**len(y)-1:
                                xs.append(y)
    if exact:
        return {x for x in xs if j <= len(x) <= k}
    return {x for x in xs if len(x) <= k}

def generate_full_alt(a, j=2, k=3, full=False):
    """
    a is an assignment
    Generates a set of clauses given an assignment (set of literals).
    """
    vs = {abs(e) for e in a}
    xs = [()]
    for x in xs:
        if len(x) < k:
            for v in vs:
                for e in [v,-v]:
                    if e not in x and -e not in x:
                        y = set(x).union({e})
                        y = tuple(sorted(y,key=abs))
                        if y not in xs:
                            if full or not all(-e in a for e in y):
                                xs.append(y)
    return {x for x in xs if j <= len(x) <= k}

def randomize_signs(xs):
    """
    Randomly flips signs maintaining the solutions as they were.
    """
    variables = list(sorted(set.union(*(set(abs(e) for e in x) for x in xs))))
    for v in variables:
        if random.choice((0,1)):
            xs_ = set()
            for x in xs:
                if v in x:
                    x = set(x).difference({v}).union({-v})
                    x = tuple(sorted(x,key=abs))
                    xs_.add(x)
                elif -v in x:
                    x = set(x).difference({-v}).union({v})
                    x = tuple(sorted(x,key=abs))
                    xs_.add(x)
                else:
                    xs_.add(x)
            xs = xs_
    return xs

def randomize_names(xs):
    """
    Randomly renames variables maintaining the solutions as they were.
    """
    variables = list(sorted(set.union(*(set(abs(e) for e in x) for x in xs))))
    new_variables = list(variables)
    random.shuffle(new_variables)
    dv = {u: v for u,v in zip(variables, new_variables)}
    for v,u in zip(new_variables,variables):
        dv[v] = u
    xs_ = set()
    for x in xs:
        x = tuple(((e > 0) - (e < 0))*dv[abs(e)] for e in x)
        x = tuple(sorted(x,key=abs))
        xs_.add(x)
    xs = xs_
    return xs

def randomize(xs):
    """
    Randomizes the content of the given clauses while maintaining structure (and solution structure).
    """
    xs = {tuple(sorted(x,key=abs)) for x in xs}
    xs = randomize_signs(randomize_names(xs))
    return xs
