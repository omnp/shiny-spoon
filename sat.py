import random
from sympy.logic.boolalg import And, Not, Xor, Equivalent
from sympy.logic.boolalg import to_cnf
from sympy import symbols
from sympy import Symbol

# Global to hold the approximate total number of top-level steps taken.
Global_Counter = 0


def add_element(x, e):
    """Add element e to clause x."""
    return clause(set(x).union({e}))


def clause(x):
    """Make a clause (sorted tuple) of an iterable."""
    return tuple(sorted(set(x), key=abs))


def complement_element(x, e):
    """Negate element e of clause x."""
    return clause(set(x).difference({e}).union({-e}))


def contains_any(x, xs):
    """True if x includes all elements of y for some y in xs."""
    return any(all(e in x for e in y) for y in xs)


def exclude_element(x, e):
    """Exclude element e from clause x."""
    return tuple(f for f in x if f != e)


def exclude_elements(x, es):
    """Exclude all elements es from clause x."""
    return tuple(f for f in x if f not in es)


def exclude_complement_elements(x, es):
    """Exclude all negations of elements es from clause x."""
    return tuple(f for f in x if -f not in es)


def exclude(xs, es):
    """
    Exclude all elements x in xs if any element of x is in es,
    otherwise exclude all negations of elements es from x.
    """
    return {
        exclude_complement_elements(x, es)
        for x in xs
        if not any(e in es for e in x)
    }


def get_literals(xs):
    """Return the set of literals in clauses xs."""
    assert xs
    return set.union(*(set(x) for x in xs))


def get_variables(xs):
    """Return the set of variables in clauses xs."""
    assert xs
    return set.union(*({abs(e) for e in x} for x in xs))


def propagate(xs, assignment):
    """
    Perform a form of unit propagation given xs and an assignment.
    return True, full_assignment, _, _ if no clauses remain with conflicts
    return False, partial_assignment, _, _ if a conflict is found
    return None, partial_assignment, literals, remaining_clauses
    if partial status
    In the last case a further (at least one) choice of
    an assigned literal needs to be done to complete
    the propagation to either True or False status.
    The choice of next element is not made by this function.
    """
    unit = set()
    value = None
    ls = set()
    while True:
        if any(-e in assignment.union(unit) for e in assignment.union(unit)):
            value = False
            # break
        xs = exclude(xs, assignment.union(unit))
        if not xs:
            if value is None:
                value = True
            break
        if not all(xs):
            value = False
            # break
        ls = get_literals(xs)
        unit_ = {e for e in ls if -e not in ls}
        for x in xs:
            if len(x) <= 1:
                for e in x:
                    unit_.add(e)
        unit = unit_.union(unit)
        ls = ls.difference(unit).difference(assignment)
        if not unit_:
            break
    return value, assignment.union(unit), ls, xs


def resolve(x, y, lt=False):
    """
    Resolve two clauses (x and y) together if possible.
    """
    if (s := sum(1 if -e in x else 0 for e in y)) == 1 or lt and s <= 1:
        z = (
            set(x)
            .difference({-e for e in y})
            .union(set(y).difference({-e for e in x}))
        )
        z = clause(z)
        return z


def preprocess(xs, limit=None, rounds=None):
    """
    Preprocess (resolve) clauses.
    """
    # xs = set(xs)
    while rounds is None or rounds > 0:
        if rounds is not None:
            rounds -= 1
        xs_ = set()
        remove = set()
        for x in xs:
            for y in xs:
                z = resolve(x, y)
                if z is not None:
                    if not any(all(-e in z for e in w) for w in xs):
                        if limit is None or len(z) <= limit:
                            if all(e in x for e in z):
                                remove.add(x)
                                xs_.add(z)
                            if all(e in y for e in z):
                                remove.add(y)
                                xs_.add(z)
        # xs = xs.union(xs_).difference(remove)
        for x in xs_:
            xs.add(x)
        for x in remove:
            xs.remove(x)
        if not xs_:
            break
    return clean(xs)


def clean(xs):
    """
    Remove redundant clauses.
    """
    for x in list(xs):
        for y in xs:
            if x != y and all(e in x for e in y):
                xs.remove(x)
                break
    return xs


def tok(cl, r=3):
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
            c0 = clause(c[:r - 1] + (i,))
            c = clause(c[r - 1:] + (-i,))
            i += 1
            cln.add(c0)
        cln.add(c)
    assert all(len(x) <= r for x in cln)
    cll = cll.union(cln)
    return cll


def to3(cl):
    """Return clauses with length at most three."""
    return tok(cl, r=3)


def generate_assignment(n):
    """
    n = number of variables
    Generates a random assignment (a set of literals).
    """
    r = list(range(1, n + 1))
    for i, e in enumerate(r):
        if random.choice((True, False)):
            r[i] = -e
    return set(r)


def generate_assignment_from_set(vs):
    """
    vs = variables
    Generates a random assignment (a set of literals).
    """
    r = list(vs)
    for i, e in enumerate(r):
        if random.choice((True, False)):
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
                for e in [v, -v]:
                    if e not in x and -e not in x:
                        y = add_element(x, e)
                        if y not in xs:
                            cluster = {
                                z
                                for z in xs
                                if {abs(f) for f in z} == {abs(f) for f in y}
                            }
                            if full or len(cluster) < 2 ** len(y) - 1:
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
                for e in [v, -v]:
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
        if random.choice((0, 1)):
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
    dv = {u: v for u, v in zip(variables, new_variables)}
    for v, u in zip(new_variables, variables):
        dv[v] = u
    xs_ = set()
    for x in xs:
        x = tuple(((e > 0) - (e < 0)) * dv[abs(e)] for e in x)
        x = tuple(sorted(x, key=abs))
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


def random_instance(n, m, k):
    """
    Generates a random instance targeted to have n variables, m clauses,
    with clause length equal to k.
    """
    xs = set()
    counter = 0
    limit = 512
    variables = tuple(range(1, 1 + n))
    while len(xs) < m:
        xs_ = set(xs)
        xs.add(
            clause(
                random.choice((1, -1)) * v
                for v in randomize_order(variables)[:k]
            )
        )
        if xs_ == xs:
            counter += 1
        else:
            counter = 0
        if counter >= limit:
            break
    return variables, xs


def partials(x):
    n = len(x)
    for i in range(2**n):
        r = list(x)
        for j, e in enumerate(r):
            if i & 1:
                r[j] = -e
            i >>= 1
        yield clause(r)


def product(xs):
    r = 1
    for x in xs:
        r *= x
    return r


def sharp_sat_enumerate(xs, a=set(), only_one=True,
                        learned=set(), limit=[1000]):
    global Global_Counter
    Global_Counter += 1
    if all(any(e in a for e in x) for x in xs):
        yield a
    else:
        limit[0] -= 1
        if limit[0] < 0:
            return
        t, a_, v, xs_ = propagate(set(xs).union(learned), set(a))
        if t is False:
            learned.add(clause(-e for e in a))
            learned_ = list(learned)
            for x in learned_:
                if x in learned:
                    learned.remove(x)
                count = 0
                for y in list(xs):
                    if (z := resolve(x, y)) is not None:
                        if len(z) <= len(y):
                            count += 1
                            if not z:
                                return
                            if z not in learned_:
                                learned_.append(z)
                if count <= 0:
                    if len(x) <= max(len(z) for z in xs):
                        xs.add(x)
            clean(xs)
            return
        if t is True:
            yield a_
            if only_one:
                return
        if t is None:
            a__ = a
            a = a_
            e = min(v, key=lambda e:
                    product(1/len(x) if e in x else 1 for x in xs))
            es = (e, -e)
            for e_ in es:
                a_ = a.union({e_})
                if not any(all(-e in a_ for e in x)
                           for x in xs.union(learned)):
                    s = sharp_sat_enumerate(xs, a_, only_one, learned, limit)
                    for x in s:
                        yield x
                        if only_one:
                            return
                a.add(-e_)
            learned.add(clause(-e for e in a__))


def driver(Xs, t=6, limit=1000):
    """
    Applies the above recursive function a number of times in different
    configurations of clauses.
    Until an assignment is found or gives up when the set limit for number
    of steps is hit.
    """
    if not isinstance(Xs, dict):
        Xs = {0: Xs}
    for u, xs in Xs.items():
        if not xs:
            return True, u
    for u, xs in list(Xs.items()):
        if not all(xs):
            del Xs[u]
    if not Xs:
        return False, None
    Variables = {}
    N = {}
    Symbols = {}
    M = 0
    for u, xs in Xs.items():
        variables = list(sorted(get_variables(xs)))
        Variables[u] = variables
        n = len(variables)
        N[u] = n
        sm = symbols(" ".join(str(v) for v in variables))
        if isinstance(sm, Symbol):
            sm = (sm,)
        Symbols[u] = sm
        M = max(M, max(variables))
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
    for k in range(0, n + 1):
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
                for i in range(1, k + 3):
                    vector = []
                    for _ in range(n):
                        vector.append(random.randint(0, 1))
                    bit = random.randint(0, 1)
                    vectors.append(vector)
                    bits.append(bit)
                aux = list(range(M + 1, M + 1 + n * (k + 2)))
                sm_aux = symbols(" ".join(str(v) for v in aux))
                sm_mapping = {}
                for s, i in zip(sm, variables):
                    sm_mapping[s] = i
                for s, i in zip(sm_aux, aux):
                    sm_mapping[s] = i
                expression = True
                for i, (vector, bit) in enumerate(zip(vectors, bits)):
                    exr = None
                    for j in range(n):
                        x = sm[j]
                        y = sm_aux[i * n + j]
                        a = vector[j] > 0
                        b = bit > 0
                        if exr is None:
                            exr = And(x, a)
                        else:
                            exr = Xor(sm_aux[i * n + j - 1], Xor(And(a, x), b))
                        exr = Equivalent(y, exr)
                    expression = And(expression, exr)
                expression = to_cnf(expression)
                if expression:
                    ys = set()
                    for clause in expression.args:
                        y = []
                        if isinstance(clause, Symbol):
                            y.append(sm_mapping[clause])
                        elif isinstance(clause, Not):
                            y.append(-sm_mapping[clause.args[0]])
                        else:
                            for literal in clause.args:
                                if isinstance(literal, Not):
                                    y.append(-sm_mapping[literal.args[0]])
                                else:
                                    y.append(sm_mapping[literal])
                        y = tuple(sorted(y, key=abs))
                        ys.add(y)
                    xs_ = Xs[u].union(ys)
                    try:
                        if (s := list(sharp_sat_enumerate(xs_, only_one=True,
                                                          limit=[limit]))):
                            return True, s
                    except ValueError:
                        pass
    return False, None


def sat(xs, **kwargs):
    """
    Main sat solving function in this module.
    xs is a set of clauses (tuples sorted by absolute value of element)
    """
    global Global_Counter
    xs = set(xs)
    r = driver(xs, 7, limit=1000)
    if r[0]:
        return True, r[1][0]
    return False, None
