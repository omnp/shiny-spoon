from sat import clause, get_variables, to3, randomize, propagate, exclude
from sat import generate_full_alt, generate_assignment, random_instance
from sat import get_literals
import php
import dimacs
import waerden
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


def rec(original_xs, additional_xs=None):
    global counter
    if additional_xs is None:
        additional_xs = set()
    targets = [()]
    while targets:
        target = targets.pop()
        counter += 1
        print(f"\x1b[2K\r\t{counter}\t{len(additional_xs)}\t{len(targets)}\t{len(target)}", end="")
        value, r, vs, _ = propagate(original_xs.union(additional_xs), set(-e for e in target))
        if value is True:
            return r
        if value is not False:
            if any(all(e in {-f for f in r} for e in x) for x in original_xs.union(additional_xs)):
                value = False
        if value is False:
            target_r = list(target)
            random.shuffle(target_r)
            for element in target_r:
                target_ = set(target).difference({element}).union({-element})
                value, r, _, _ = propagate(original_xs.union(additional_xs), set(-e for e in target_))
                if value is True:
                    return r
                if value is False:
                    target = tuple(e for e in target if e != element)
            if not target:
                return None
            additional_xs.add(clause(target))
            clean(additional_xs)
            for t in list(targets):
                if all(e in t for e in target):
                    targets.remove(t)
            if target:
                i = len(target) - 1
                while i >= 0:
                    if target[i] < 0:
                        break
                    i -= 1
                if i >= 0 and target[i] < 0:
                    target_ = target[0:i] + (-target[i],) + target[i+1:]
                    assert target_ not in targets
                    targets.append(target_)
            continue
        v = max(vs, key=lambda v: max(len({v, -v}.union(target).intersection(x)) for x in (additional_xs or original_xs)))
        v = -abs(v)
        target_ = target + (v,)
        if target_ not in targets:
            assert not any(all(e in target_ for e in x) for x in original_xs)
            assert not any(all(e in target_ for e in x) for x in additional_xs)
            assert not any(all(e in target_ for e in x) for x in targets)
            targets.append(target_)


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
    # xs = php.php(6, 6)
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
    xs = php.php(7, 6)
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
    # xs = to3(xs)
    # xs = waerden.waerden(3, 5, 22)
    print(len(xs), len(get_variables(xs)))
    xs = randomize(xs)
    counter = 0
    r = rec(xs)
    print(r, counter)
    ## exit()
    # u = 12
    # v = 12
    # n = u*v
    # xsp = php.php(u, v)
    # xsp = to3(xsp)
    # xsp = randomize(xsp)
    # n = len(get_variables(xsp))
    # s = generate_assignment(n)
    counter = 0
    # s = rec(set(xsp))
    # counter = 0
    # xs = generate_full_alt(s, j=4, k=4, full=True)
    # xs = generate_full_alt(s, j=3, k=7, full=True)
    # xs = generate_full_alt(s, j=2, k=2, full=True)
    # xsp = php.php(u, v)
    # xsp = randomize(xsp)
    # xs = xs.union(xsp)
    # ts = set()
    # ts = {clause(s)}

    # for _ in range(1):
        # t = generate_assignment(n)
        # t = generate_assignment_php(n)
        # while clause(t) in ts:
        # while clause(t) in ts:
            # t = generate_assignment(n)
        # ts.add(clause(t))
        # xs = {x for x in xs if not all(-e in t for e in x)}
    # for t in ts:
    #     xs = {x for x in xs if not all(-e in t for e in x)}
    # xs = xs.union(xsp)
    # print("ts", len(ts))
    # _, xs = random_instance(128, 10000, 7)
    # with open("examples/factoring2017-0002.dimacs") as file:
    # with open("examples/factoring2017-0003.dimacs") as file:
    # with open("examples/factoring2017-0004.dimacs") as file:
    # with open("examples/factoring2017-0005.dimacs") as file:
    # with open("examples/factoring2017-0006.dimacs") as file:
    # with open("examples/factoring2017-0001.dimacs") as file:
    # with open("examples/factoring2017.dimacs") as file:
    #     text = file.read()
    #     file.close()
    #     _, xs = dimacs.parse_dimacs(text)
    #     xs = {clause(set(x)) for x in xs}
    ratio = 4.27
    n = 128 # 1722 # 192 # 256 # 314 # 134 # 314
    m = int(n * ratio)
    k = 3
    print(f"Clauses to variables ratio: {ratio}, with {n} variables and {m} clauses....")
    print(f"(Clause length: {k})")

    from sat import randomize_order

    def random_instance_given_assignments(n, m, k, assignments=None):
        """
        Generates a random instance targeted to have n variables, m clauses,
        with clause length equal to k.
        """
        if assignments is None:
            assignments = set()
        xs = set()
        counter = 0
        limit = 512
        variables = tuple(range(1, 1 + n))
        while len(xs) < m:
            xs_ = set(xs)
            x = clause(
                    random.choice((1, -1)) * v
                    for v in randomize_order(variables)[:k]
                )
            if not any(all(-e in s for e in x) for s in assignments):
                xs.add(x)
            if xs_ == xs:
                counter += 1
            else:
                counter = 0
            if counter >= limit:
                break
        return variables, xs

    s = clause(generate_assignment(n))
    _, xs = random_instance_given_assignments(n, m, k, {s})
    # _, xs = random_instance(n, m, k)
    # _, xs = random_instance(128, 10000, 7)
    # xs = waerden.waerden(4, 5, 55)
    # xs = waerden.waerden(4, 5, 54)
    # xs = waerden.waerden(3, 5, 21)
    # xs = waerden.waerden(3, 5, 22)
    print(len(xs), len(get_variables(xs)))
    xs = set(xs)
    # xs = randomize(xs)
    counter = 0
    total = 0
    vs = get_variables(xs)
    # xs = to3(xs)
    print(len(xs), len(get_variables(xs)))
    xs_ = set(xs)
    rs_ = set()
    additional_xs = set()
    while True:
        counter_ = counter
        r = rec(xs, additional_xs)
        if r is not None:
            total += 1
        print("\n\t", r is not None, counter - counter_, total)
        if r is None:
            break
        xs.add(clause(-e for e in r if abs(e) in vs))
        rs_.add(clause(-e for e in r if abs(e) in vs))
        # xs = to3(xs)
        clean(xs)
        clean(additional_xs)
    counter = 0
    if rs_:
        rs_.pop()
    r = rec(xs_.union(rs_))
    print("\n\t", r is not None, counter, total)


if __name__ == '__main__':
    main()
