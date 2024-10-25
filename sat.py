import random

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
    xs = set(xs)
    while rounds is None or rounds > 0:
        if rounds is not None:
            rounds -= 1
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
        yield r


def sat_wrapped(xs, assignment=set(), **kwargs):
    global Global_Counter
    Global_Counter += 1
    truth, assignment, literals, xs_ = propagate(set(xs), assignment)
    if truth is True:
        return assignment
    if truth is False:
        return None
    if not any(e > 0 for e in literals):
        return assignment.union(literals)
    literals = {e for e in literals if e > 0}
    e = min(literals)
    x = min({x for x in xs_ if e in x}, key=len)
    for i, e in enumerate(x):
        if not any(all(-f in assignment.union({e}) for f in y) for y in xs): 
            s = sat_wrapped(
                xs, assignment.union({e}).union({-e for e in x[:i]}))
            if s is not None:
                return s
    return None


def sat(xs, **kwargs):
    """
    Main sat solving function in this module.
    xs is a set of clauses (tuples sorted by absolute value of element)
    """
    s = sat_wrapped(xs)
    return s is not None, s
