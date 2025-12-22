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
def rec(original_xs, additional_xs=None):
    global counter
    if additional_xs is None:
        additional_xs = set()
    targets = additional_xs
    target = ()
    xs = set(original_xs)
    while True:
        counter += 1
        print(f"\x1b[2K\r\t{counter}\t{len(additional_xs)}\t{len(targets)}\t{len(target)}", end="")
        value, r, vs, xs = propagate(xs.union(targets), {-e for e in target})
        if value is True:
            return r
        if any(all(e in target for e in x) for x in xs.union(targets)):
            value = False
        while value is False:
            if not target:
                return None
            targets.add(clause(target))
            clean(targets)
            target = target[:-1] + (-target[-1],)
            if clause(target) in targets or any(all(e in target for e in x) for x in targets):
                target = target[:-1]
            xs = set(original_xs)
            value, r, vs, xs = propagate(xs.union(targets), {-e for e in target})
            if value is True:
                return r
            if any(all(e in target for e in x) for x in xs.union(targets)):
                value = False
        if value is None:
            x = max(xs, key=len)
            target = target + x


@update_additional_clauses
def symmetry_breaking(xs, additional_xs=None):
    global counter
    if additional_xs is None:
        additional_xs = set()

    # variables = list(sorted(get_variables(xs)))
    # scores = {}
    # for v in variables:
    #     for v_ in v, -v:
    #         scores[v_] = 1
    # increment = 1

    def exchange_vars(xs, a, b):
        if isinstance(a, int) and isinstance(b, int):
            result_xs = set()
            for x in xs:
                x_ = tuple(sorted(((e > 0)-(e < 0))*b if e == a else ((e > 0)-(e < 0))*a if e == b else e for e in x))
                result_xs.add(x_)
        else:
            result_xs = set(xs)
        return result_xs

    def exchange_vars_mapping(mapping, a, b):
        mapping[a] = b
        mapping[-a] = -b
        return mapping

    def get_lit(mapping, e):
        if e in mapping:
            return mapping[e]
        return e

    xs = set(xs)
    xss = [xs]
    mappings = [{}]
    assignments = [set()]
    non_renameable_pairs = set()

    while xss and mappings:
        counter += 1
        xs = xss.pop()
        mapping = mappings.pop()
        assignment = assignments.pop()
        print(f"\x1b[2K\r\t{counter}\t{len(additional_xs)}\t{len(xs)}\t{len(assignment)}", end="")
        xs_after = set()
        for x in sorted(xs, key=len, reverse=True):
            for i, e in enumerate(x):
                if abs(e) not in mapping:
                    for f in x[i+1:]:
                        if abs(f) not in mapping:
                            xs_ = exchange_vars(xs, e, f)
                            if xs != xs_:
                                non_renameable_pairs.add((e, f))
                            else:
                                mapping[f] = e
                    break
            else:
                continue
            break
        xs_after = {tuple(sorted({get_lit(mapping, e) for e in x})) for x in xs}
        value, r, vs, xs_ = propagate(xs_after, assignment)
        if value is True:
            return r
        if value is False:
            return None
        if xs_after == xs:
            v = min(vs, key=abs)
            for v in v, -v:
                value, r, _, xs_ = propagate(xs_after, assignment.union({v}))
                if value is True:
                    return r
                if value is False:
                    continue
                xss.append(xs_)
                mappings.append(mapping)
                assignments.append(r)
        else:
            xss.append(xs_)
            mappings.append(mapping)
            assignments.append(r)


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
    stats = []
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
        stats.append((len(xs), counter - counter_))
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
