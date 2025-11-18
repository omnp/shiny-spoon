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


def rec(original_xs):
    global counter
    targets = [()]
    while targets:
        targets.sort(reverse=True)
        target = targets.pop()
        counter += 1
        print(f"\x1b[2K\r\t{counter}\t{len(targets)}\t{len(target)}", end="")
        value, r, vs, _ = propagate(original_xs, set(-e for e in target))
        if value is True:
            return r
        if value is not False:
            if any(all(e in {-f for f in r} for e in x) for x in original_xs):
                value = False
        if value is False:
            for element in reversed(target):
                target_ = set(target).difference({element}).union({-element})
                value, r, _, _ = propagate(original_xs, set(-e for e in target_))
                if value is True:
                    return r
                if value is False:
                    target = tuple(e for e in target if e != element)
            if not target:
                return None
            original_xs.add(clause(target))
            clean(original_xs)
            for t in list(targets):
                if all(e in t for e in target):
                    targets.remove(t)
            continue
        v = max(vs, key=lambda v: max(len({v, -v}.union(target).intersection(x)) for x in original_xs))
        target_ = target + (-v,)
        if target_ not in targets:
            targets.append(target_)    
        target_ = target + (v,)
        if target_ not in targets:
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
    xs_ = set(xs)
    rs_ = set()
    while True:
        counter_ = counter
        r = rec(xs)
        if r is not None:
            total += 1
        print("\n\t", r is not None, counter - counter_, total)
        if r is None:
            break
        xs.add(clause(-e for e in r if abs(e) in vs))
        rs_.add(clause(-e for e in r if abs(e) in vs))
        clean(xs)
    counter = 0
    if rs_:
        rs_.pop()
    r = rec(xs_.union(rs_))
    print("\n\t", r is not None, counter, total)


if __name__ == '__main__':
    main()
