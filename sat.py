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

I = 0
def sat(xs):
    if not xs:
        return True, set()
    if not all(xs):
        return False, None
    _xs_ = set(xs)
    Depth = 0
    def resolve(target, a=set(), depth=0):
        """
            Recursive procedure for checking unsatisfiability. Whether target can be resolved from the given clauses.
        """
        global I
        nonlocal Depth
        nonlocal _xs_
        depth += 1
        I += 1
        Depth = max(Depth, depth)
        if target in _xs_ or any(all(e in target for e in x) for x in _xs_):
            #print('target (in orig. set)', target, *(x for x in _xs_ if all(e in target for e in x)))
            return {target}
        else:
            xs = {tuple(e for e in x if -e not in a) for x in _xs_ if not any(e in a for e in x)}
            xs_ = [x for x in xs if any(sum(1 if -e in x else 0 for e in y) == 1 for y in xs)]
            if xs_:
                literals = set.union(*(set(x) for x in xs_))
                nn = {e for e in literals if -e not in literals}
                literals = literals.difference({e for e in target}).difference({-e for e in target}).difference(nn)
                if not literals:
                    return None
                e = max(sorted(literals,key=abs),key=lambda e:sum(1 if e in x else 0 for x in xs_))
                b = tuple(sorted(set(target).union({e}),key=abs))
                c = tuple(sorted(set(target).union({-e}),key=abs))
                u = v = None
                u = resolve(b, a.union({-e}).union(nn), depth)
                if u is not None:
                    v = resolve(c, a.union({e}).union(nn), depth)
                if u is None or v is None:
                    return None
                return {target}
    target = ()
    Depth = 0
    r = resolve(target)
    return not(r is not None and () in r), r

def wrapper(xs, variables=None):
    """
    Tries to generate a valid assignment, given one exists.
    """
    xs = {tuple(sorted(x,key=abs)) for x in xs}
    clauses = set(xs)
    t = sat(clauses)
    if t[0]:
        variables = variables or list(sorted(set.union(*(set(abs(e) for e in x) for x in clauses))))
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
