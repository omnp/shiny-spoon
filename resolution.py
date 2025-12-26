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


def preprocess(xs, initial_mapping=None, random_mapping=None):
    import random
    if random_mapping is None:
        random_mapping = False
    if initial_mapping is None:
        initial_mapping = {}
    vs = list(sorted(get_variables(xs)))
    mapping = dict(initial_mapping)
    lits = list(vs)
    if not random_mapping:
        while True:
            mapping_ = dict(mapping)
            counts = {v: 0 for v in vs}
            for x in xs:
                for e in x:
                    counts[abs(e)] += 1
            lits.sort(key=lambda v: counts[v], reverse=True)
            for u, v in zip(lits, vs):
                mapping = map(mapping, u, v)
            if mapping_ == mapping:
                break
            xs = apply(mapping, xs)
    else:
        random.shuffle(lits)
        for u, v in zip(lits, vs):
            mapping = map(mapping, u, v)
    return mapping


def identity(xs):
    from sat import get_literals
    vs = list(sorted(get_literals(xs)))
    mapping = {v: v for v in vs}
    return mapping


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
    assignments = [set()]
    all_assignments = set()
    scores = {v: 0 for v in get_literals(xs)}
    increment = 1

    def update_scores(x):
        nonlocal scores
        nonlocal increment
        for v in x:
            scores[v] += increment
        increment += 1

    while assignments:
        counter += 1
        clean(additional_xs)
        assignment = assignments.pop()
        xs = original_xs.union(additional_xs)
        initial_mapping = preprocess(xs, random_mapping=False)
        inverse_initial_mapping = invert(initial_mapping)
        xs = apply(initial_mapping, xs)
        value, r, vs, xs = propagate(xs, {initial_mapping[e] for e in assignment})
        print(f"\x1b[2K\r\t{counter}\t{len(additional_xs)}\t{len(xs)}\t{len(assignment)}", end="")
        if value is True:
            r = {inverse_initial_mapping[e] for e in r}
            return r
        if value is False:
            t = clause(-f for f in assignment)
            for x in original_xs.union(additional_xs):
                y = resolve(t, x)
                if y is not None and len(y) < len(t):
                    t = y
            additional_xs.add(t)
            update_scores(tuple(e for e in t))
            continue
        count_mapping = preprocess(xs, random_mapping=False)
        inverse_count_mapping = invert(count_mapping)
        xs = apply(count_mapping, xs)
        found = False
        found_element = None
        xs_ = {x for x in xs if all(1 >= sum(1 if e in y else 0 for y in xs) for e in x)}
        for x in xs_:
            found = True
            for i, element in enumerate(x):
                found = True
                mapping = dict()
                for e in x[i+1:]:
                    map(mapping, e, element)
                    map(mapping, element, e)
                    connections = get_literals(xs).difference(x).difference({-f for f in x})
                    try:
                        for a in connections:
                            for b in connections:
                                if abs(a) != abs(b):
                                    if a not in mapping and b not in mapping and -a not in mapping and -b not in mapping:
                                        if a not in mapping.values() and b not in mapping.values() and -a not in mapping.values() and -b not in mapping.values():
                                            mapping_ = dict(mapping)
                                            map(mapping_, b, a)
                                            map(mapping_, a, b)
                                            xs__ = apply(mapping_, xs)
                                            if xs__ == xs:
                                                mapping = mapping_
                                                raise ValueError
                    except ValueError:
                        continue
                    found = False
                    break
                if found:
                    found_element = element
                    break
            if found:
                break
        if found:
            # print(f"element: {found_element}")
            element = found_element
            value, r_, _, xs_ = propagate(xs.union(apply(count_mapping, apply(initial_mapping, additional_xs))), set(apply_clause(count_mapping, r)).union({element}))
            if value is True:
                r_ = set(apply_clause(inverse_count_mapping, r_))
                r_ = {inverse_initial_mapping[e] for e in r_}
                return r_
            if value is False:
                t = clause(-f for f in assignment.union({inverse_initial_mapping[inverse_count_mapping[element]]}))
                for x in original_xs.union(additional_xs):
                    y = resolve(t, x)
                    if y is not None and len(y) < len(t):
                        t = y
                additional_xs.add(t)
                update_scores(tuple(e for e in t))
                continue
            t = clause(assignment.union({inverse_initial_mapping[inverse_count_mapping[element]]}))
            if t not in all_assignments:
                all_assignments.add(t)
                assignments.append(set(t))
        else:
            vs = {inverse_initial_mapping[v] for v in vs}
            v = max(vs, key=lambda v: scores[v])
            vs = list(u for u in vs if scores[u] >= scores[v])
            vs = list(count_mapping[initial_mapping[v]] for v in vs)
            v = min(vs, key=abs)
            # print("v", v)
            for v in -v, v:
                value_, r_, _, xs_ = propagate(xs.union(apply(count_mapping, apply(initial_mapping, additional_xs))), set(apply_clause(count_mapping, r)).union({v}))
                if value_ is True:
                    r_ = set(apply_clause(inverse_count_mapping, r_))
                    r_ = {inverse_initial_mapping[e] for e in r_}
                    return r_
                if value_ is False:
                    t = clause(-f for f in assignment.union({inverse_initial_mapping[inverse_count_mapping[v]]}))
                    for x in original_xs.union(additional_xs):
                        y = resolve(t, x)
                        if y is not None and len(y) < len(t):
                            t = y
                    additional_xs.add(t)
                    update_scores(tuple(e for e in t))
                    continue
                t = clause(assignment.union({inverse_initial_mapping[inverse_count_mapping[v]]}))
                if t not in all_assignments:
                    all_assignments.add(t)
                    assignments.append(set(t))


def main():
    import sys  # For command line arguments
    global counter
    random.seed(1)
    ratio = 4.27
    n = 110
    m = int(math.ceil(n * ratio))
    k = 3
    h = 3  # <= Number of satisfying assignments

    from sat import randomize_order, generate_assignment, partials, randomize

    def random_instance_given_assignments(n, m=None, k=None, assignments=None, clustered=None):
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

    # s = {clause(generate_assignment(n)) for _ in range(h)}
    # _, xs = random_instance_given_assignments(n, m, k, s)
    # _, xs = random_instance_given_assignments(n, None, k, s)
    # _, xs = random_instance_given_assignments(n, None, k, s, clustered=True)
    # _, xs = random_instance_given_assignments(n, m, k)
    # _, xs = random_instance_given_assignments(n, None, k)
    _, xs = random_instance_given_assignments(n, None, k, clustered=True)
    # import php
    # xs = php.php(5, 4)
    # xs = php.php(4, 4)
    # import waerden
    # xs = waerden.waerden(3, 5, 21)
    # xs = waerden.waerden(4, 5, 54)
    # with open("examples/factoring2017-0006.dimacs") as file:
        # import dimacs
        # text = file.read()
        # _, xs = dimacs.parse_dimacs(text)
        # xs = {clause(set(x)) for x in xs if not any(-e in x for e in x)}
    xs = randomize(xs)
    print(len(xs), len(get_variables(xs)))
    xs = set(xs)
    counter = 0
    total = 0
    vs = get_variables(xs)
    rs_ = []
    additional_xs = set()
    split = False
    args = list(sys.argv[1:])
    if args and "split" in args:
        args.remove("split")
        split = True

    while True:
        counter_ = counter
        r = symmetry_breaking(xs, additional_xs)
        if r is not None:
            r = {e for e in r if abs(e) in vs}
            for v in vs:
                if -v not in r:
                    r.add(v)
                if v not in r:
                    r.add(-v)
            total += 1
        print("\n\t", r is not None, all(r is None or any(e in r for e in x) for x in xs), counter - counter_, total)
        if r is None:
            break
        r = clause(-e for e in r if abs(e) in vs)
        if split:
            r = list(r)
            random.shuffle(r)
            r = clause(r[:k])
        xs.add(r)
        if r not in rs_:
            rs_.append(r)


if __name__ == '__main__':
    main()
