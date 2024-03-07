import math
import random
from sympy.logic.boolalg import And, Not, Xor, Equivalent
from sympy.logic.boolalg import to_cnf
from sympy import symbols
from sympy import Symbol

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

I = 0 # Global to hold the total number of recursive steps taken.
def sat(xs, MaxRecSteps=None):
    if not xs:
        return True, set()
    if not all(xs):
        return False, None
    _xs_ = set(xs)
    Depth = 0
    J = 0
    def resolve(target, a=set(), depth=0):
        """
            Recursive procedure for checking unsatisfiability. Whether target can be resolved from the given clauses.
        """
        global I
        nonlocal J
        nonlocal Depth
        nonlocal _xs_
        nonlocal MaxRecSteps
        depth += 1
        I += 1
        J += 1
        if MaxRecSteps is not None and J >= MaxRecSteps:
            return {target}
        Depth = max(Depth, depth)
        if target in _xs_ or any(all(e in target for e in x) for x in _xs_):
            return {target}
        else:
            xs = {tuple(e for e in x if -e not in a) for x in _xs_ if not any(e in a for e in x)}
            if not xs:
                return None
            if not all(xs):
                return {target}
            xs_ = [x for x in xs if any(sum(1 if -e in x else 0 for e in y) == 1 for y in xs)]
            if xs_:
                literals = set.union(*(set(x) for x in xs_))
                nn = {e for e in literals if -e not in literals}
                literals = literals.difference(nn)
                if not literals:
                    return None
                e = min(sorted(literals,key=abs),key=lambda e:sum(1 if e in x else 0 for x in xs_))
                b = tuple(sorted(set(target).union({-e}),key=abs))
                c = tuple(sorted(set(target).union({e}),key=abs))
                u = v = None
                u = resolve(b, a.union({e}).union(nn), depth)
                if u is None:
                    return None
                v = resolve(c, a.union({-e}).union(nn), depth)
                if v is None:
                    return None
                return {target}
    target = ()
    Depth = 0
    r = resolve(target)
    return not(r is not None and () in r), r

_sat = sat
def driver(Xs, t = 6):
    """
    Applies the above recursive function a number of times in different configurations of clauses.
    Until an assignment is found or gives up when the set limit for number of steps is hit.
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
        variables = list(sorted(set.union(*(set(abs(e) for e in x) for x in xs))))
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
    The following section is inspired by the following blog post which explains in some detail
    the practical application of the Valiant-Vazirani theorem:
        https://lucatrevisan.wordpress.com/2010/04/29/cs254-lecture-7-valiant-vazirani/

    All errors and misunderstandings in the following implementation are entirely my own.
    This code is also the reason why (a part of) the sympy package is now imported and required.
    """
    for k in range(0,n+1):
        for t_ in range(t):
            for u in Xs:
                """
                This bit (iterating u's) is an addition where we check both positive and negative literal
                one after the other on each step.
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
                    K = 1 + int(math.log(len(xs_))/math.log(2))
                    print(f'\rt k', '\t',t_,'\t',k,'\t',K,'\t',2**K,'\t',len(xs_),'\t',len(Xs[u]), end='')
                    if _sat(xs_, 2**K)[0]:
                        print()
                        return True, u
    print()
    return False, None

sat = driver
def wrapper(xs, variables=None):
    """
    Tries to generate a valid assignment, given one exists.
    """
    xs = {tuple(sorted(x,key=abs)) for x in xs}
    clauses = set(xs)
    t = sat({0: preprocess(clauses)})
    if t[0]:
        variables = variables or list(sorted(set.union(*(set(abs(e) for e in x) for x in clauses))))
        result = set()
        for v in sorted(variables,key=abs):
            Cs = {}
            literals = list(sorted(set.union(*(set(e for e in x) for x in clauses)),key=abs))
            for u in [v,-v]:
                if u in literals:
                    cs = {tuple(e for e in x if -e not in result.union({u})) for x in clauses if not any(e in result.union({u}) for e in x)}
                    Cs[u] = preprocess(cs)
            t = sat(Cs)
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

def resolve(x,y):
    if sum(1 if -e in x else 0 for e in y) == 1:
        z = set(x).difference({-e for e in y}).union(set(y).difference({-e for e in x}))
        z = tuple(sorted(z,key=abs))
        return z

def preprocess(xs):
    """
    Undo the process of the to3 (tok) function(s).
    """
    xs = set(xs)
    while True:
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
        xs = xs.union(xs_)
        if not xs_:
            break
    while True:
        xs_ = set()
        remove = set()
        for x in list(xs):
            for y in list(xs):
                if x in xs and y in xs:
                    z = resolve(x, y)
                    if z is not None:
                        if all(e in x for e in z):
                            remove.add(x)
                            xs_.add(z)
                        if all(e in y for e in z):
                            remove.add(y)
                            xs_.add(z)
        xs = xs.union(xs_).difference(remove)
        if not xs_:
            break
    return xs

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
