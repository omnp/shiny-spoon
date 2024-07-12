import random
from sympy.logic.boolalg import And, Not, Xor, Equivalent
from sympy.logic.boolalg import to_cnf
from sympy import symbols
from sympy import Symbol

def add_element(x, e):
    return clause(set(x).union({e}))

def clause(x):
    return tuple(sorted(set(x),key=abs))

def complement_element(x, e):
    return clause(set(x).difference({e}).union({-e}))

def contains_any(x, xs):
    return any(all(e in x for e in y) for y in xs)

def exclude_element(x, e):
    return tuple(f for f in x if f != e)

def exclude_elements(x, es):
    return tuple(f for f in x if f not in es)

def exclude_complement_elements(x, es):
    return tuple(f for f in x if -f not in es)

def exclude(xs, es):
    return {exclude_complement_elements(x, es) 
            for x in xs if not any(e in es for e in x)}

def get_literals(xs):
    assert(xs)
    return set.union(*(set(x) for x in xs))

def get_variables(xs):
    assert(xs)
    return set.union(*({abs(e) for e in x} for x in xs))

def propagate(xs, assignment):
    unit = set()
    value = None
    ls = set()
    while True:
        if any(-e in assignment.union(unit) for e in assignment.union(unit)):
            value = False
            break
        xs = exclude(xs, assignment.union(unit))
        if not xs:
            value = True
            break
        if not all(xs):
            value = False
            break
        ls = get_literals(xs)
        unit_ = {e for e in ls if -e not in ls}
        for x in xs:
            if len(x) <= 1:
                for e in x: unit_.add(e)
        unit = unit_.union(unit)
        ls = ls.difference(unit).difference(assignment)
        if not unit_:
            break
    return value, assignment.union(unit), ls, xs

def tuple_less_than(x,y):
    return tuple(abs(e) for e in x) < tuple(abs(e) for e in y)

I = 0 # Global to hold the total number of recursive steps taken.
def sat(xs, MaxRecSteps=None):
    if not xs:
        return True, set()
    if not all(xs):
        return False, None
    J = 0
    def recursive(a = set()):
        """
        Recursive procedure for checking satisfiability. 
        """
        global I
        nonlocal xs, J, MaxRecSteps
        I += 1
        J += 1
        print(f'\r{J}', end='')
        if MaxRecSteps is not None and J >= MaxRecSteps:
            raise ValueError
        value, a, vs, xs_ = propagate(set(xs), a)
        if value is True:
            return True, a
        if value is False:
            return False, None
        forced = {}
        forced_by = {}
        for v in vs:
            if v not in forced:
                forced[v] = set()
            for x in xs_:
                if -v in x:
                    if len(x) <= 2:
                        for e in x:
                            if e != -v:
                                forced[v].add(e)
                if v in x:
                    if v not in forced_by:
                        forced_by[v] = set()
                    forced_by[v].add(tuple(-e for e in x if e != v))
        v = max(vs, key = lambda v: len(set.intersection(*(set(y) for y in forced_by[v]))))
        vs_ = {u for u in vs if len(set.intersection(*(set(y) for y in forced_by[u]))) >= len(set.intersection(*(set(y) for y in forced_by[v])))}
        v = min(vs_,key=abs)
        for v in (v,-v):
            if v in vs:
                i = set.intersection(*(set(y) for y in forced_by[v]))
                a_ = a.union({v}).union(i).union(forced[v])
                val, a_, _, _ = propagate(set(xs_), a_)
                if val is True:
                    return True, a_
                elif val is None:
                    r = recursive(a_)
                    if r[0]:
                        return r
        return False, None
    return recursive()

def driver(Xs, t = 6):
    """
    Applies the above recursive function a number of times in different 
    configurations of clauses.
    Until an assignment is found or gives up when the set limit for number 
    of steps is hit.
    """
    global J
    if type(Xs) != dict:
        Xs = {0: Xs}
    for u,xs in Xs.items():
        if not xs:
            return True, u
    for u,xs in list(Xs.items()):
        if not all(xs):
            del Xs[u]
    if not Xs:
        return False, None
    Variables = {}
    N = {}
    Symbols = {}
    M = 0
    for u,xs in Xs.items():
        variables = list(sorted(get_variables(xs)))
        Variables[u] = variables
        n = len(variables)
        N[u] = n
        sm = symbols(' '.join(str(v) for v in variables))
        if type(sm) == Symbol:
            sm = (sm,)
        Symbols[u] = sm
        M = max(M,max(variables))
    n = max(N.values())
    """
    The following section is inspired by the following blog post which explains
      in some detail the practical application of the Valiant-Vazirani theorem:
    
https://lucatrevisan.wordpress.com/2010/04/29/cs254-lecture-7-valiant-vazirani/

    All errors and misunderstandings in the following implementation are 
    entirely my own.
    This code is also the reason why (a part of) the SymPy package is now 
    imported and required.
    """
    for k in range(0,n+1):
        for t_ in range(t):
            for u in Xs:
                """
                This bit (iterating u's) is an addition where we check both 
                positive and negative literal one after the other on each step.
                """
                variables = Variables[u]
                sm = Symbols[u]
                n = N[u]
                """
                And back to limiting the number of assignments:
                """
                vectors = []
                bits = []
                for i in range(1,k+3):
                    vector = []
                    for _ in range(n):
                        vector.append(random.randint(0,1))
                    bit = random.randint(0,1)
                    vectors.append(vector)
                    bits.append(bit)
                aux = list(range(M+1,M+1+n*(k+2)))
                sm_aux = symbols(' '.join(str(v) for v in aux))
                sm_mapping = {}
                for s,i in zip(sm, variables):
                    sm_mapping[s] = i
                for s,i in zip(sm_aux,aux):
                    sm_mapping[s] = i
                expression = True
                for i,(vector,bit) in enumerate(zip(vectors,bits)):
                    exr = None
                    for j in range(n):
                        x = sm[j]
                        y = sm_aux[i*n+j]
                        a = vector[j] > 0
                        b = bit > 0
                        if exr is None:
                            exr = And(x, a)
                        else:
                            exr = Xor(sm_aux[i*n+j-1], Xor(And(a, x), b))
                        exr = Equivalent(y,exr)
                    expression = And(expression,exr)
                expression = to_cnf(expression)
                if expression:
                    ys = set()
                    for clause in expression.args:
                        y = []
                        if type(clause) == Symbol:
                            y.append(sm_mapping[clause])
                        elif type(clause) == Not:
                            y.append(-sm_mapping[clause.args[0]])
                        else:
                            for literal in clause.args:
                                if type(literal) == Not:
                                    y.append(-sm_mapping[literal.args[0]])
                                else:
                                    y.append(sm_mapping[literal])
                        y = tuple(sorted(y,key=abs))
                        ys.add(y)
                    xs_ = Xs[u].union(ys)
                    m = len(xs_)
                    print(f'\rt k', '\t',t_,'\t',k,'\t',m,'\t',len(xs_),
                          '\t',len(Xs[u]), end='')
                    try:
                        if (s := sat(xs_, m))[0]:
                            print()
                            return s
                    except ValueError:
                        pass
    print()
    return False, None

def driver_wrapper(xs, variables=None):
    """
    Tries to generate a valid assignment, given one exists.
    """
    xs = {clause(x) for x in xs}
    clauses = set(xs)
    t = driver({0: preprocess(clauses)})
    if t[0]:
        variables = variables or list(sorted(get_variables(clauses)))
        result = set()
        for v in sorted(variables,key=abs):
            Cs = {}
            literals = list(sorted(get_literals(clauses),key=abs))
            for u in [v,-v]:
                if u in literals:
                    cs = exclude(clauses, result.union({u}))
                    Cs[u] = preprocess(cs)
            if not Cs:
                result.add(v)
                continue
            t = driver(Cs)
            if t[0]:
                u = t[1]
                print('v',u)
                result.add(u)
            else:
                print(Cs)
                print(v)
                raise ValueError
        return result
    return set()

def wrapper(xs, variables=None):
    """
    Tries to generate a valid assignment, given one exists.
    """
    xs = {clause(x) for x in xs}
    clauses = set(xs)
    t = sat(clauses)
    if t[0]:
        variables = variables or list(sorted(get_variables(clauses)))
        result = set()
        for v in sorted(variables,key=abs):
            if not clauses:
                result.add(v)
                continue
            literals = list(sorted(get_literals(clauses),key=abs))
            if v in literals:
                cs = exclude(clauses, result.union({v}))
                t = sat(cs)
                if t[0]:
                    print('v',v)
                    result.add(v)
                    clauses = cs
                else:
                    print('v',-v)
                    result.add(-v)
            else:
                print('v',-v)
                result.add(-v)
        return result
    return set()

def resolve(x,y,lt=False):
    if (s := sum(1 if -e in x else 0 for e in y)) == 1 or lt and s <= 1:
        z = set(x).difference({-e for e in y}).union(
            set(y).difference({-e for e in x}))
        z = clause(z)
        return z

def preprocess(xs, limit=None, undo=False):
    """
    Undo the process of the to3 (tok) function(s).
    """
    xs = set(xs)
    while undo:
        xs_ = set()
        for x in list(xs):
            for y in list(xs):
                if x in xs and y in xs:
                    z = resolve(x, y)
                    if z is not None:
                        for e in set(x).difference(set(z)):
                            if sum(1 if e in w or -e in w else 0 for w in xs) == 2:
                                xs.remove(x)
                                xs.remove(y)
                                xs_.add(z)
                                break
        xs = xs.union(xs_)
        if not xs_:
            break
    while True:
        xs_ = set()
        remove = set()
        for x in xs:
            for y in xs:
                z = resolve(x, y)
                if z is not None and (limit is None or len(z) <= limit):
                    if all(e in x for e in z):
                        remove.add(x)
                        xs_.add(z)
                    if all(e in y for e in z):
                        remove.add(y)
                        xs_.add(z)
        xs = xs.union(xs_).difference(remove)
        if not xs_:
            break
    return clean(xs)

def clean(xs):
    for x in list(xs):
        for y in xs:
            if x != y and all(e in x for e in y):
                xs.remove(x)
                break
    return xs

def tok(cl,r=3):
    """
    cl is a set of clauses
    r >= 3
    This function generates a set of clauses where the length of each clause 
    is at most r.
    """
    if not cl:
        return set()
    vs = get_variables(cl)
    i = max(vs) + 1
    cll = {x for x in cl if len(x) <= r}
    cl = cl.difference(cll)
    cln = set()
    for c in cl:
        c = clause(c)
        while len(c) > r:
            c0 = clause(c[:r-1] + (i,))
            c = clause(c[r-1:] + (-i,))
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
    Generates a set of clauses containing the given clauses as a solution 
    (which may be empty).
    """
    vs = get_variables(xs)
    xs = list(xs)
    for x in xs:
        if len(x) < k:
            for v in vs:
                for e in [v,-v]:
                    if e not in x and -e not in x:
                        y = add_element(x, e)
                        if y not in xs:
                            cluster = {z for z in xs if {abs(f) for f in z} == {abs(f) for f in y}}
                            if full or len(cluster) < 2**len(y)-1:
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
                        y = add_element(x, e)
                        if y not in xs:
                            if full or not all(-e in a for e in y):
                                xs.append(y)
    return {x for x in xs if j <= len(x) <= k}

def randomize_signs(xs):
    """
    Randomly flips signs maintaining the solutions as they were.
    """
    variables = list(sorted(get_variables(xs)))
    for v in variables:
        if random.choice((0,1)):
            xs_ = set()
            for x in xs:
                if v in x:
                    x = complement_element(x, v)
                    xs_.add(x)
                elif -v in x:
                    x = complement_element(x, -v)
                    xs_.add(x)
                else:
                    xs_.add(x)
            xs = xs_
    return xs

def randomize_names(xs):
    """
    Randomly renames variables maintaining the solutions as they were.
    """
    variables = list(sorted(get_variables(xs)))
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
    Randomizes the content of the given clauses while maintaining structure 
    (and solution structure).
    """
    xs = {clause(x) for x in xs}
    xs = randomize_signs(randomize_names(xs))
    return xs

def randomize_order(variables):
    """
    Shuffles a tuple.
    """
    variables = list(variables)
    random.shuffle(variables)
    return tuple(variables)

def random_instance(n,m,k):
    """
    Generates a random instance targeted to have n variables, m clauses, 
    with clause length equal to k.
    """
    xs = set()
    counter = 0
    limit = 512
    variables = tuple(range(1,1+n))
    while len(xs) < m:
        xs_ = set(xs)
        xs.add(clause(random.choice((1,-1)) * v for v in randomize_order(variables)[:k]))
        if xs_ == xs:
            counter += 1
        else:
            counter = 0
        if counter >= limit:
            break
    return variables, xs

def rec_sat(xs, a = set()):
    global I
    I += 1
    assert(not(any(-e in a for e in a)))
    if not xs:
        return True, a
    if not(all(xs)):
        return False, None
    z = min(xs,key=lambda x:tuple(abs(e) for e in x))
    for v in z:
        xsv = {x for x in xs if v in x}
        xsn = {x for x in xs if v not in x}
        ands = {tuple(-e for e in x if e != v) for x in xsv}
        ors = {tuple(e for e in x if e != -v) for x in xsn}
        i = set.intersection(*(set(x) for x in ands))
        ands = {tuple(e for e in x if e not in i) for x in ands}
        for x in ands:
             assert(-v not in x)
             a_ = a.union({v}).union(x).union(i)
             ors_ = {tuple(e for e in y if -e not in a_) for y in ors if not any(e in a_ for e in y)}
             t,s = rec_sat(ors_, a_)
             if t:
                 return t,s
    return False, None

def sat(xs, MaxRecSteps=None):
    return rec_sat(xs)
