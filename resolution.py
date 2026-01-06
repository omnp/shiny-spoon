from sat import clause, get_variables, propagate
from functools import wraps
import random
import math


def clean(xs):
    """
    Remove redundant clauses.
    """
    tree = {}
    leaves = set()
    for x in sorted(xs, key=len):
        tree_ = tree
        for e in x:
            if e in tree_:
                if isinstance(tree_[e], tuple) or isinstance(tree_[e], frozenset):
                    break
                tree_ = tree_[e]
        else:
            tree_ = tree
            for i, e in enumerate(x):
                if e not in tree_:
                    if i < len(x)-1:
                        tree_[e] = {}
                    else:
                        tree_[e] = x
                        leaves.add(x)
                tree_ = tree_[e]
    xs.clear()
    xs.update(leaves)
    return xs


def update_additional_clauses(fn):
    @wraps(fn)
    def wrap(*args, **kwargs):
        old_additional_clauses = None
        additional_clauses = None
        if len(args) >= 2:
            if isinstance(args[1], set):
                old_additional_clauses = set(args[1])
                additional_clauses = args[1]
        elif 'additional_xs' in kwargs:
            if isinstance(kwargs['additional_xs'], set):
                old_additional_clauses = set(kwargs['additional_xs'])
                additional_clauses = kwargs['additional_xs']
        result = fn(*args, **kwargs)
        if old_additional_clauses is not None:
            additional_clauses.difference_update(old_additional_clauses)
        return result

    return wrap


def map(mapping, a, b):
    mapping[a] = b
    mapping[-a] = -b
    return mapping


def invert(mapping):
    inverse = {}
    for k, v in mapping.items():
        inverse[v] = k
    return inverse


def apply_clause(mapping, x):
    x = clause(set(mapping[e] if e in mapping else e for e in x))
    return x


def apply(mapping, xs):
    xs = {apply_clause(mapping, x) for x in xs}
    return xs


def apply_map(mapping, other):
    result = {k: other[v] if v in other else v for k, v in mapping.items()}
    return result


def preprocess(xs, one=None):
    from collections import defaultdict
    if one is None:
        one = False
    signatures = defaultdict(lambda: defaultdict(int))
    for c in xs:
        for lit in c:
            signatures[lit][len(c)] += 1

    sig_cache = {lit: tuple(sorted(sig.items())) for lit, sig in signatures.items()}
    inv_sig_cache = defaultdict(lambda: set())
    for k, v in sig_cache.items():
        inv_sig_cache[v].add(k)

    xs = set(frozenset(c) for c in xs)
    symmetric_elements = {}
    vs = set(signatures)

    for element in vs:
        if element in symmetric_elements:
            continue
        y = inv_sig_cache[sig_cache[element]]
        for e in set(y).difference({element}):
            if sig_cache[element] != sig_cache[e]:
                continue
            mapping = dict()
            map(mapping, e, element)
            map(mapping, element, e)
            connections = vs.difference({element}).difference({e})
            n = sum(1 if frozenset(apply_clause(mapping, c)) in xs else 0 for c in xs)
            try:
                for a in connections:
                    for b in inv_sig_cache[sig_cache[a]]:
                        mapping_ = dict(mapping)
                        if abs(a) != abs(b):
                            map(mapping_, b, a)
                            map(mapping_, a, b)
                        else:
                            map(mapping_, b, a)
                        m = sum(1 if frozenset(apply_clause(mapping_, c)) in xs else 0 for c in xs)
                        if n <= m:
                            n = m
                            mapping = mapping_
                        if n >= len(xs):
                            raise ValueError
            except ValueError:
                if element not in symmetric_elements:
                    symmetric_elements[element] = set()
                symmetric_elements[element].add(e)
        if element in symmetric_elements:
            for e in symmetric_elements[element]:
                if e not in symmetric_elements:
                    symmetric_elements[e] = set()
                symmetric_elements[e].update(symmetric_elements[element])

    for element in vs:
        e = -element
        mapping = dict()
        map(mapping, e, element)
        connections = vs.difference({element}).difference({e})
        n = sum(1 if frozenset(apply_clause(mapping, c)) in xs else 0 for c in xs)
        try:
            for a in connections:
                for b in inv_sig_cache[sig_cache[a]]:
                    mapping_ = dict(mapping)
                    if abs(a) != abs(b):
                        map(mapping_, b, a)
                        map(mapping_, a, b)
                    else:
                        map(mapping_, b, a)
                    m = sum(1 if frozenset(apply_clause(mapping_, c)) in xs else 0 for c in xs)
                    if n <= m:
                        n = m
                        mapping = mapping_
                    if n >= len(xs):
                        raise ValueError
        except ValueError:
            if element not in symmetric_elements:
                symmetric_elements[element] = set()
            if e not in symmetric_elements[element]:
                symmetric_elements[element].add(e)

    return symmetric_elements


def multi_invert(mapping):
    inverse = {}
    for k, v in mapping.items():
        if v not in inverse:
            inverse[v] = set()
        inverse[v].add(k)
    return inverse


def multi_apply_clause(mapping, x):
    x = clause(set.union(*(mapping[e] if e in mapping else {e} for e in x)))
    return x


def multi_apply(mapping, xs):
    xs = {multi_apply_clause(mapping, x) for x in xs}
    return xs


@update_additional_clauses
def symmetry_breaking(xs, additional_xs=None):
    from sat import get_literals, resolve
    global counter
    if additional_xs is None:
        additional_xs = set()

    if not xs:
        return set()
    if not all(xs):
        return None

    original_xs = set(xs)
    scores = {v: 0 for v in get_literals(xs)}
    increment = 1

    def update_scores(x):
        nonlocal scores
        nonlocal increment
        for v in x:
            scores[v] += increment
        increment /= 0.90
        if increment > 1e100:
            for v in scores:
                scores[v] *= 1e-100
            increment *= 1e-100

    def restart(level=None):
        nonlocal assignments
        nonlocal initial_assignment
        if level is None:
            assignments.clear()
            assignments.append(dict(initial_assignment))
        else:
            for x in list(assignments):
                if x.values() and max(x.values()) > level:
                    assignments.remove(x)

    initial_assignment = {}
    assignments = [dict(initial_assignment)]
    mapping = {}
    inverse = multi_invert(mapping)
    symmetric_elements = preprocess(original_xs.union(additional_xs), one=False)
    print(len(symmetric_elements), sum(len(v) for v in symmetric_elements.values()))

    while assignments:
        counter += 1
        clean(additional_xs)
        assignment = assignments.pop()
        level = max(assignment.values(), default=0)
        xs = original_xs.union(additional_xs)
        value, r, vs, xs = propagate(xs, set(assignment))
        print(f"\x1b[2K\r\t{counter}\t{len(additional_xs)}\t{len(assignments)}\t{len(assignment)}", end="")
        if value is True:
            tmp_xs = multi_apply(inverse, additional_xs)
            additional_xs.clear()
            additional_xs.update(tmp_xs)
            r = multi_apply_clause(inverse, r)
            return r
        if value is False:
            t = set(assignment)
            for e in reversed(list(t)):
                t_ = t.difference({e})
                value_, _, _, _ = propagate(original_xs.union(additional_xs), set(t_))
                if value_ is False:
                    t = t_
            for a in list(assignments):
                if all(e in a for e in t):
                    assignments.remove(a)
            t = clause(-f for f in t)
            for x in original_xs.union(additional_xs):
                y = resolve(t, x)
                if y is not None and len(y) < len(t):
                    if y not in additional_xs:
                        t = y
            if not t:
                return None
            up = multi_apply_clause(inverse, {-e for e in t})
            update_scores({abs(e) for e in up})
            additional_xs.add(t)
            continue
        for v in vs:
            if v in symmetric_elements:
                if -v in symmetric_elements[v]:
                    print(f"v {v}")
                    vs = {v}
                    break
        else:
            for v in list(vs):
                if v in vs:
                    if any(e in symmetric_elements and v in symmetric_elements[e] or -e in symmetric_elements and -v in symmetric_elements[-e] for e in r):
                        if -v in vs:
                            vs.remove(v)
        v = max(vs, key=lambda v: (scores[abs(min(inverse[v]))] if v in inverse else scores[abs(v)]))
        vs = list(u for u in vs if (scores[abs(min(inverse[u]))] if u in inverse else scores[abs(u)]) >= (scores[abs(min(inverse[v]))] if v in inverse else scores[abs(v)]))
        v = min(vs, key=abs)
        for v in -v, v:
            if v not in vs:
                continue
            assignment_v = dict(assignment)
            assignment_v[v] = level + 1
            assignments.append(assignment_v)


def random_instance_given_assignments(n, m=None, k=None, assignments=None, clustered=None):
    from sat import randomize_order, partials
    """
    Generates a random instance targeted to have n variables, m clauses,
    with clause length equal to k.
    """
    if clustered is None:
        clustered = False
    if assignments is None:
        assignments = set()
    if k is None:
        k = 3
    if m is None:
        m = math.inf
    xs = set()
    counter = 0
    limit = 512
    variables = tuple(range(1, 1 + n))
    if clustered:
        clusters = {tuple(range(i, min(1 + n, i + k))) for i in range(1, 1 + n, k)}
        generators = {}
        for cluster in clusters:
            generators[cluster] = partials(cluster)
        while len(xs) < m:
            n_ = len(xs)
            for cluster in generators:
                try:
                    x = next(generators[cluster])
                    if not any(all(-e in s for e in x) for s in assignments):
                        if len(xs) < m:
                            xs.add(x)
                except StopIteration:
                    pass
            if n_ == len(xs):
                counter += 1
            else:
                counter = 0
            if counter >= limit:
                break
        return variables, xs
    while len(xs) < m:
        n_ = len(xs)
        x = clause(
                random.choice((1, -1)) * v
                for v in randomize_order(variables)[:k]
            )
        if not any(all(-e in s for e in x) for s in assignments):
            xs.add(x)
        if n_ == len(xs):
            counter += 1
        else:
            counter = 0
        if counter >= limit:
            break
    return variables, xs
