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


def preprocess(xs, one=None):
    if one is None:
        one = False
    original_xs = set(xs)
    symmetric_elements = set()
    symmetric_clauses = set()
    initial_assignment = {}
    level = 0
    while True:
        level += 1
        xs = original_xs
        value, r, vs, xs = propagate(xs, set(initial_assignment))
        if value is True:
            break
        if value is False:
            break
        found_elements = set()
        vs.difference_update(symmetric_elements)
        for element in sorted(vs, key=lambda v: sum(1 if v in x else 0 for x in xs)):
            if element not in vs:
                continue
            found = True
            xs_ = {y for y in xs if element in y}
            y = set.union(*(set(y) for y in xs_))
            for e in set(y).difference({element}).difference(symmetric_elements):
                mapping = dict()
                map(mapping, e, element)
                map(mapping, element, e)
                connections = vs.difference({element}).difference({e})
                n = sum(1 if apply_clause(mapping, c) in xs else 0 for c in xs)
                try:
                    for a in connections:
                        for b in connections:
                            if abs(a) != abs(b):
                                mapping_ = dict(mapping)
                                map(mapping_, b, a)
                                map(mapping_, a, b)
                            else:
                                mapping_ = dict(mapping)
                                map(mapping_, b, a)
                            m = sum(1 if apply_clause(mapping_, c) in xs else 0 for c in xs)
                            if n <= m:
                                n = m
                                mapping = mapping_
                            if n >= len(xs):
                                raise ValueError
                except ValueError:
                    continue
                found = False
                break
            if found:
                found_elements.add(element)
                found_elements.update(y)
                vs.difference_update(found_elements)
                symmetric_clauses.update(xs_)
                if one:
                    break
        if found_elements:
            symmetric_elements.update(found_elements)
        else:
            break
        if one:
            break
    return initial_assignment, symmetric_elements, symmetric_clauses


def preprocess_negative(xs, one=None):
    if one is None:
        one = False
    original_xs = set(xs)
    symmetric_elements = set()
    initial_assignment = {}
    level = 0
    while True:
        level += 1
        xs = original_xs
        value, r, vs, xs = propagate(xs, set(initial_assignment))
        if value is True:
            break
        if value is False:
            break
        found_elements = set()
        vs.difference_update(symmetric_elements)
        for element in sorted(vs, key=lambda v: sum(1 if v in x else 0 for x in xs)):
            mapping = dict()
            map(mapping, -element, element)
            connections = vs.difference({element}).difference({-element})
            n = sum(1 if apply_clause(mapping, c) in xs else 0 for c in xs)
            try:
                for a in connections:
                    for b in connections:
                        if abs(a) != abs(b):
                            mapping_ = dict(mapping)
                            map(mapping_, b, a)
                            map(mapping_, a, b)
                        else:
                            mapping_ = dict(mapping)
                            map(mapping_, b, a)
                        m = sum(1 if apply_clause(mapping_, c) in xs else 0 for c in xs)
                        if n <= m:
                            n = m
                            mapping = mapping_
                        if n >= len(xs):
                            raise ValueError
            except ValueError:
                found_elements.add(element)
                if one:
                    break
        if found_elements:
            symmetric_elements.update(found_elements)
        else:
            break
        if one:
            break
    return initial_assignment, symmetric_elements


@update_additional_clauses
def symmetry_breaking(xs, additional_xs=None):
    from sat import exclude, get_literals, resolve
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
    _, symmetric_elements, _ = preprocess(xs, one=False)
    _, negative_symmetric = preprocess_negative(xs, one=False)

    while assignments:
        counter += 1
        clean(additional_xs)
        assignment = assignments.pop()
        level = max(assignment.values(), default=0)
        xs = original_xs.union(additional_xs)
        value, r, vs, xs = propagate(xs, set(assignment))
        print(f"\x1b[2K\r\t{counter}\t{len(additional_xs)}\t{len(xs)}\t{len(assignment)}", end="")
        if value is True:
            return r
        if value is False:
            t = set(assignment)
            for e in reversed(list(t)):
                t_ = t.difference({e})
                value_, _, _, _ = propagate(original_xs.union(additional_xs), set(t_))
                if value_ is False:
                    t = t_
            t = clause(-f for f in t)
            for x in original_xs.union(additional_xs):
                y = resolve(t, x)
                if y is not None and len(y) < len(t):
                    if y not in additional_xs:
                        t = y
            update_scores(tuple(-e for e in t))
            additional_xs.add(t)
            continue
        for v in symmetric_elements:
            if v in vs:
                if len({abs(e) for e in vs}) > 1:
                    print(f"found symmetric element {v}")
                vs = {v}
                break
        for v in negative_symmetric:
            if v in vs:
                if len({abs(e) for e in vs}) > 1:
                    print(f"found negative symmetric element {v}")
                vs = {v}
                break
        v = max(vs, key=lambda v: scores[abs(v)])
        vs = list(u for u in vs if scores[abs(u)] >= scores[abs(v)])
        v = min(vs, key=abs)
        for v in -v, v:
            if v not in vs:
                continue
            assignment_v = dict(assignment)
            assignment_v[v] = level + 1
            assignments.append(assignment_v)


def main():
    import sys  # For command line arguments
    global counter
    random.seed(1)
    ratio = 4.27
    n = 110
    m = int(math.ceil(n * ratio))
    k = 3
    h = 3  # <= Number of satisfying assignments

    from sat import randomize_order, generate_assignment, partials, randomize, resolve

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
        for x in xs:
            y = resolve(r, x)
            if y is not None and len(y) < len(r):
                r = y
        xs.add(r)
        if r not in rs_:
            rs_.append(r)


if __name__ == '__main__':
    main()
