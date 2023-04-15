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

MaxAll = 0 # This global variable is for collecting a statistic.

def sat(xs, original_variables, AllRejects=None, p=True):
    """
    xs is a collection of tuples, sets or lists (must be 3-CNF, all clauses in three or less variables).
    This function iterates through all the
        (n choose 3) * 2**3 + (n choose 2) * 2**2 + (n choose 1) * 2**1
    number of combinations of possible assignments of at most 3 variables at a time
    and learns clauses from conflicts (resolutions to the empty clause).
    """
    global MaxAll
    xs = [tuple(sorted(set(x), key=abs)) for x in xs]
    if not all(xs):
        return False, xs, None
    if len(xs) <= 1:
        return True, xs, None
    vs_ = set.union(*(set(x) for x in xs))
    vs = {abs(e) for e in vs_}.intersection(original_variables)
    N = max(len(x) for x in xs)
    if p: print('\t', end='')
    All = set(xs)
    Rejects = set()
    if AllRejects is not None:
        All, Rejects = AllRejects
        All = set(All)
        Rejects = set(Rejects)
    def rec(abc, k=3):
        """
        Recursion (up to depth k) to find conflicts and add clauses.
        """
        m = 0
        if abc:
            m = max(abc)
        for a in {a for a in vs if a >= m}:
            abc_ = abc.union({a})
            if p: print('\r',*('\t{:4}'.format(e) for e in sorted(abc_)), end='')    
            s = 0
            w = set()
            if sum(1 if any(abs(e) in abc_ for e in x) else 0 for x in xs) <= 1:
                continue
            for fgh in partials(abc_,full=True):
                if p: print('\r',*('\t{:4}'.format(e) for e in fgh), end='')
                if any(all(e in fgh for e in x) for x in Rejects):
                    s += 1
                    continue
                xs__ = set(xs)
                xs__ = {tuple(e for e in x if -e not in fgh) for x in xs if not any(e in fgh for e in x)}
                All__ = set(All)
                while () not in xs__:
                    foundany = False
                    for x in list(xs__):
                        if len(x) <= N-1:
                            for y in list(xs__):
                                if len(y) <= N:
                                    if sum(1 if -e in x else 0 for e in y) == 1:
                                        z = set(x).difference({-e for e in y}).union(set(y).difference({-e for e in x}))
                                        z = tuple(sorted(z,key=abs))
                                        if len(z) <= N-1:
                                            if z not in All__:
                                                xs__.add(z)
                                                All__.add(z)
                                                foundany = True
                                                break
                    for x in list(xs__):
                        for y in xs__:
                            if all(e in x for e in y):
                                if x != y:
                                    xs__.remove(x)
                                    break
                    if not foundany:
                        break
                if () in xs__:
                    Rejects.add(fgh)
                    s += 1
                    t = tuple(sorted((-e for e in fgh),key=abs))
                    if t not in xs:
                        xs.append(t)
                        All.add(t)
                else:
                    w.add(fgh)
            if w:
                w = set.union(*(set(a) for a in w))
                w = {e for e in w if -e not in w}
                for e in w:
                    if (e,) not in xs:
                        xs.append((e,))
            if s == 2**len(abc_):
                if () not in xs:
                    xs.append(())
            for x in list(xs):
                if len(x) <= N-1:
                    for y in list(xs):
                        if sum(1 if -e in x else 0 for e in y) == 1:
                            z = set(x).difference({-e for e in y}).union(set(y).difference({-e for e in x}))
                            z = tuple(sorted(z,key=abs))
                            if len(z) <= N-1:
                                if z not in All:
                                    xs.append(z)
                                    All.add(z)
            for x in list(xs):
                for y in xs:
                    if all(e in x for e in y):
                        if x != y:
                            xs.remove(x)
                            break
        if () not in xs and k > 1:
            for a in {a for a in vs if a >= m}:
                abc_ = abc.union({a})
                rec(abc_, k-1)
    rec(set(),k=3)
    if p: print('\t{}'.format(len(All)))
    MaxAll = max(MaxAll, len(All))
    return () not in xs, xs, (All, Rejects)

def wrapper(clauses, original_variables):
    """
    Tries to generate a valid assignment, given one exists.
    """
    clauses = {tuple(sorted(x,key=abs)) for x in clauses}
    variables = list(sorted(set.union(*(set(abs(e) for e in x) for x in clauses))))
    t = sat(clauses, original_variables)
    if t[0]:
        clauses = t[1]
        AR = t[2]
        result = set()
        for v in original_variables:
            for u in [v,-v]:
                cs = {tuple(sorted((e for e in x if e != -u), key=abs)) for x in clauses if u not in x}
                t = sat(cs, original_variables, AR)
                if t[0]:
                    result.add(u)
                    clauses = t[1]
                    AR = t[2]
                    break
            else:
                raise BaseException
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
    clusters = {}
    for x in cl:
        k = tuple(sorted({abs(e) for e in x}))
        if k not in clusters:
            clusters[k] = set()
        clusters[k].add(x)
    cll = {x for x in cl if len(x) <= r}
    cl = cl.difference(cll)
    cln = set()
    for j in list(clusters):
        for c in clusters[j]:
            c = tuple(sorted(c,key=abs))
            while len(c) > r:
                c0 = tuple(sorted(c[:2] + (i,),key=abs))
                c = tuple(sorted(c[2:] + (-i,),key=abs)) 
                cln.add(c0)
                i += 1
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

def generate_full(xs, k=3):
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
                            xs.append(y)
    return {x for x in xs if len(x) == k}

def generate_full_alt(a, k=3, full=False):
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
    return {x for x in xs if len(x) == k}

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
