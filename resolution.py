from sat import clause, get_variables, randomize, propagate
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
    targets = [()]
    while targets:
        target = targets.pop()
        counter += 1
        print(f"\x1b[2K\r\t{counter}\t{len(additional_xs)}\t{len(targets)}\t{len(target)}", end="")
        value, r, _, _ = propagate(original_xs.union(additional_xs), {e for e in target})
        if value is True:
            return r
        value, r, vs, xs = propagate(original_xs.union(additional_xs), {-e for e in target})
        if value is True:
            return r
        if value is False:
            i = len(target)-1
            while i > 0:
                target_ = target[:i] + (-target[i],) + target[i+1:]
                value, r, _, _ = propagate(original_xs.union(additional_xs), {-e for e in target_})
                if value is True:
                    return r
                if value is False:
                    target = tuple(e for j, e in enumerate(target) if j != i)
                i -= 1
            for t in list(targets):
                if all(e in t for e in target):
                    targets.remove(t)
            additional_xs.add(clause(target))
            for t in list(additional_xs):
                if t != clause(target) and all(e in t for e in target):
                    additional_xs.remove(t)
            continue
        vs = min(xs, key=len)
        for v in sorted(vs, key=abs, reverse=True):
            target_ = target + (-v,)
            if target_ not in targets:
                if not any(all(e in target_ for e in t) for t in targets):
                    targets.append(target_)
            target = target + (v,)


def main():
    import sys  # For command line arguments
    global counter
    random.seed(1)
    ratio = 4.27
    n = 100
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

    s = clause(generate_assignment(n))
    _, xs = random_instance_given_assignments(n, m, k, {s})
    # _, xs = random_instance_given_assignments(n, None, k, {s})
    # _, xs = random_instance_given_assignments(n, m, k)
    # _, xs = random_instance_given_assignments(n, None, k)
    print(len(xs), len(get_variables(xs)))
    xs = set(xs)
    counter = 0
    total = 0
    vs = get_variables(xs)
    xs_ = set(xs)
    rs_ = []
    additional_xs = set()
    stats = []
    split = False
    if len(sys.argv) > 1 and sys.argv[1] == "split":
        split = True
    while True:
        counter_ = counter
        r = rec(xs, additional_xs)
        if r is not None:
            total += 1
        print("\n\t", r is not None, counter - counter_, total)
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
        clean(xs)
        clean(additional_xs)
    reverse_stats = []
    while rs_:
        counter = 0
        rs_.pop()
        size = len(xs_.union(rs_))
        r = rec(xs_.union(rs_))
        print("\n\t", r is not None, counter, size)
        reverse_stats.append((size, counter))
    max_forward = max(stats, key=lambda t: t[1])
    max_reverse = max([(None, 0)] + reverse_stats, key=lambda t: t[1])
    print(f"Maximums: {max_forward} (forward), {max_reverse} (reverse)")


if __name__ == '__main__':
    main()
