from sat import clause, get_variables, to3, randomize, propagate, exclude
from sat import generate_full_alt, generate_assignment, random_instance
import php
import dimacs
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
                if isinstance(tree_[e], tuple):
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


def rename(xs, u, v):
    xs_ = set()
    for x in xs:
        x_ = []
        for e in x:
            if abs(e) == abs(u):
                x_.append(((e > 0) - (e < 0)) * v)
            else:
                x_.append(e)
        x = tuple(sorted(x_, key=abs))
        xs_.add(x)
    return xs_


def minimize(xs, s):
    t = list(sorted(s, key=abs))
    cs = set()
    for e in t:
        t_ = list(t)
        t_.remove(e)
        c = None
        for e_ in list(t_):
            t__ = list(t_)
            t__.remove(e_)
            value, s_, _, _ = propagate(set(xs), set(t__))
            if value is True:
                return s_
            if value is False:
                c = clause({-e for e in t__})
            else:
                break
            t_ = t__
        if c is not None:
            cs.add(c)
            if len(xs) <= 0 or () in xs:
                break
            break
    xs.update(cs)
    return None


def preprocess(xs, reverse=None, from_one=None):
    if reverse is None:
        reverse = True
    if from_one is None:
        from_one = False
    vs_dict = {}
    vs = get_variables(xs)
    for v in vs:
        vs_dict[v] = sum(1 if v in x else 0 for x in xs)
    if from_one is True:
        vsr = list(range(1, len(vs)+1))
    else:
        vsr = list(sorted(vs))
#     us = list(sorted(vs, key=lambda v: vs_dict[v], reverse=reverse))
    us = list(sorted(vs))
    map = {u: v for u, v in zip(us, vsr)}
    for u, v in list(map.items()):
        map[-u] = -v
    for u in {abs(u) for u in map}:
        v = map[u]
        if sum(1 if v in x else 0 for x in xs) < sum(1 if -v in x else 0 for x in xs):
            map[u] = -v
            map[-u] = v
    xs_ = set()
    for x in xs:
        x = tuple(map[e] for e in x)
        x = tuple(sorted(x, key=abs))
        xs_.add(x)
    xs.clear()
    xs.update(xs_)
    return xs, map


def rec(original_xs, w=None, memory=None):
    global counter
    counter += 1
    if memory is None:
        memory = set()
    if w is None:
        w = set()
    xs = set(original_xs)
    value, r, _, xs = propagate(xs, w)
    print(f"\x1b[2K\r\t{counter}\t{len(xs)}", end="")
    key, map_ = preprocess(set(xs), reverse=True, from_one=True)
    key = frozenset(key)
    if key in memory or any(all(x in key for x in k) for k in memory):
        value = False
    if value is False:
#         original_xs.add(clause(-e for e in w))
#         minimize(original_xs, clause(-e for e in w))
#         clean(original_xs)
        if not any(all(x in key for x in k) for k in memory):
            for k in list(memory):
                if all(x in k for x in key):
                    memory.remove(k)
            memory.add(key)
            clean(memory)
        return None
    if value is True:
        return r
    vs = get_variables(xs)
    v = min(vs)
#     for v in (v, -v):
    vs_ = set()
    for v in sorted(vs):
        value, s, _, xs_ = propagate(xs, r.union({v}))
        if value is False:
            r.add(-v)
            continue
        if value is True:
            return s
        if value is None:
            vs_.add(v)
    if not vs_:
        if not any(all(x in key for x in k) for k in memory):
            for k in list(memory):
                if all(x in k for x in key):
                    memory.remove(k)
            memory.add(key)
            clean(memory)
        return None
    v = min(vs_)
    for v in (v, -v):
#     for v in sorted(vs_):
        value, s, _, xs_ = propagate(xs, r.union({v}))
        if value is False:
            r.add(-v)
            continue
        else:
            t = s
        if value is None:
            t = rec(original_xs, t, memory=memory)
        if t is not None:
            value, s, _, _ = propagate(original_xs, t)
            if value is False:
                continue
            if value is True:
                t = s
            if value is None:
                t = rec(original_xs, s, memory=memory)
            if t is not None:
                for e in get_variables(original_xs):
                    if -e not in t:
                        t.add(e)
                assert not any(-e in t for e in t)
                assert len(t) >= len(get_variables(original_xs))
                assert all(any(e in t for e in x) for x in original_xs)
                return t
#     original_xs.add(clause(-e for e in w))
#     minimize(original_xs, clause(-e for e in w))
#     clean(original_xs)
    if not any(all(x in key for x in k) for k in memory):
        for k in list(memory):
            if all(x in k for x in key):
                memory.remove(k)
        memory.add(key)
        clean(memory)


def main():
    global counter
    random.seed(1)
    # xs = php.php(1, 2)
    # xs = php.php(2, 2)
    # xs = php.php(1, 3)
    # xs = php.php(2, 3)
    # xs = php.php(3, 3)
    # xs = php.php(4, 4)
    # xs = php.php(5, 5)
    xs = php.php(6, 6)
    # xs = php.php(7, 7)
    # xs = php.php(8, 8)
    # xs = php.php(9, 9)
    # xs = php.php(16, 16)
    # xs = php.php(24, 24)
    # xs = php.php(48, 48)
    # xs = php.php(72, 72)
    # xs = php.php(92, 92)
    # xs = php.php(99, 99)
    # xs = php.php(3, 2)
    # xs = php.php(4, 3)
    # xs = php.php(5, 4)
    # xs = php.php(6, 5)
    # xs = php.php(7, 6)
    # xs = php.php(8, 7)
    # xs = php.php(9, 8)
    # xs = php.php(10, 9)
    # xs = php.php(11, 10)
    # xs = php.php(12, 11)
    # xs = php.php(15, 14)
    # xs = php.php(19, 18)
    # xs = php.php(21, 20)
    # xs = php.php(25, 24)
    # xs = php.php(31, 30)
    # xs = php.php(42, 41)
    # xs.pop()
    # for x in xs:
    #     if all(e < 0 for e in x):
    #         xs.remove(x)
    #         break
    print(len(xs), len(get_variables(xs)))
    xs = randomize(xs)
    counter = 0
    r = rec(xs)
    print(r, counter)
    ## exit()
    # n = 9
    # s = generate_assignment(n)
    # xs = generate_full_alt(s, j=4, k=4, full=True)
    # ts = set()
    # for _ in range(21):
    #     t = generate_assignment(n)
    #     while clause(t) in ts:
    #         t = generate_assignment(n)
    #     ts.add(clause(t))
    #     xs = {x for x in xs if not all(-e in t for e in x)}
    # print("ts", len(ts))
    # print(len(xs), len(get_variables(xs)))
    # _, xs = random_instance(128, 10000, 7)
    # with open("examples/factoring2017-0002.dimacs") as file:
    # with open("examples/factoring2017-0003.dimacs") as file:
    # with open("examples/factoring2017-0004.dimacs") as file:
    # with open("examples/factoring2017-0005.dimacs") as file:
    with open("examples/factoring2017-0006.dimacs") as file:
    # with open("examples/factoring2017-0001.dimacs") as file:
    # with open("examples/factoring2017.dimacs") as file:
        text = file.read()
        file.close()
        _, xs = dimacs.parse_dimacs(text)
        xs = {clause(set(x)) for x in xs}
    xs = set(xs)
    # xs = randomize(xs)
    counter = 0
    # r = rec(xs)
    # print(r, counter)
    total = 0
    vs = get_variables(xs)
    # xs = to3(xs)
    memory = set()
    xs_ = set(xs)
    rs_ = set()
    while True:
        counter = 0
        r = rec(xs, memory=memory)
        if r is not None:
            total += 1
        print("\n\t", r is not None, counter, total)
        if r is None:
            break
        xs.add(clause(-e for e in r if abs(e) in vs))
        rs_.add(clause(-e for e in r if abs(e) in vs))
        clean(xs)
    counter = 0
    if rs_:
        rs_.pop()
    r = rec(xs_.union(rs_), memory=set())
    print("\n\t", r is not None, counter, total)


if __name__ == '__main__':
    main()

