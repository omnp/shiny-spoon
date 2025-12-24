from sat import clause, get_variables, propagate
from sat import generate_assignment
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


@update_additional_clauses
def symmetry_breaking(xs, additional_xs=None):
    from sat import get_literals
    global counter
    if additional_xs is None:
        additional_xs = set()

    if not xs:
        return set()
    if not all(xs):
        return None

    def exchange_vars(xs, mapping):
        result_xs = set(xs)
        for a, b in mapping.items():
            result_xs = set()
            for x in xs:
                x_ = tuple(sorted((((e > 0)-(e < 0))*abs(b) if abs(e) == abs(a) else ((e > 0)-(e < 0))*abs(a) if abs(e) == abs(b) else e for e in x), key=abs))
                result_xs.add(x_)
            xs = result_xs
        return result_xs

    def exchange_vars_mapping(mapping, a, b):
        mapping[a] = b
        mapping[-a] = -b
        return mapping

    def get_lit(mapping, e):
        if e in mapping:
            return mapping[e]
        if -e in mapping:
            return -mapping[-e]
        return e

    xs = set(xs)
    xss = [xs]
    assignments = [set()]

    while xss:
        counter += 1
        clean(additional_xs)
        xs = xss.pop()
        assignment = assignments.pop()
        value, r, vs, xs = propagate(xs.union(additional_xs), assignment)
        print(f"\x1b[2K\r\t{counter}\t{len(additional_xs)}\t{len(xs)}\t{len(assignment)}", end="")
        if value is True:
            return r
        if value is False:
            additional_xs.add(clause(-f for f in assignment))
            continue
        x = max(xs, key=len)
        found = True
        element = None
        mapping = dict()
        for i, element in enumerate(x):
            for e in x[i+1:]:
                exchange_vars_mapping(mapping, e, element)
                exchange_vars_mapping(mapping, element, e)
                connections = get_literals(xs).difference(x).difference({-f for f in x})
                try:
                    for a in connections:
                        for b in connections:
                            if abs(a) != abs(b):
                                if a not in mapping and b not in mapping and -a not in mapping and -b not in mapping:
                                    if a not in mapping.values() and b not in mapping.values() and -a not in mapping.values() and -b not in mapping.values():
                                        mapping_ = dict(mapping)
                                        exchange_vars_mapping(mapping_, b, a)
                                        exchange_vars_mapping(mapping_, a, b)
                                        xs__ = exchange_vars(xs,  mapping_)
                                        if xs__ == xs:
                                            mapping = mapping_
                                            raise ValueError
                except ValueError:
                    continue
                found = False
        if found:
            value, r_, _, xs_ = propagate(xs.union(additional_xs), r.union({element}))
            if value is True:
                return r_
            if value is False:
                additional_xs.add(clause(-f for f in assignment.union({element})))
                continue
            if xs_ not in xss:
                xss.append(xs_)
                assignments.append(r_)
        else:
            v = min(vs, key=abs)
            for v in v, -v:
                value_, r_, _, xs_ = propagate(xs.union(additional_xs), r.union({v}))
                if value_ is True:
                    return r_
                if value_ is False:
                    additional_xs.add(clause(-e for e in assignment.union({v})))
                    continue
                if xs_ not in xss:
                    xss.append(xs_)
                    assignments.append(r_)


def main():
    import sys  # For command line arguments
    global counter
    random.seed(1)
    ratio = 4.27
    n = 110
    m = int(math.ceil(n * ratio))
    k = 3
    print(f"Clauses to variables ratio: {ratio}, with {n} variables and {m} clauses....")
    print(f"(Clause length: {k})")

    from sat import randomize_order

    def random_instance_given_assignments(n, m=None, k=None, assignments=None):
        """
        Generates a random instance targeted to have n variables, m clauses,
        with clause length equal to k.
        """
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

    # s = clause(generate_assignment(n))
    # _, xs = random_instance_given_assignments(n, m, k, {s})
    # _, xs = random_instance_given_assignments(n, None, k, {s})
    _, xs = random_instance_given_assignments(n, m, k)
    # _, xs = random_instance_given_assignments(n, None, k)
    #
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
