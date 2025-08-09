from sat import clause, get_variables, exclude, to3, randomize, propagate, clean
import php
import dimacs
import random


def preprocess(xs):
    if not xs:
        return xs
    vs = get_variables(xs)
    vs = list(sorted(vs))
    vs_sorted = list(sorted(vs, key=lambda v: sum(1 if v in x or -v in x else 0 for x in xs)))
    vs_dict = {v: u for u, v in zip(vs, vs_sorted)}
    xs_ = set()
    for x in xs:
        x_ = clause(((e > 0)-(e < 0)) * vs_dict[abs(e)] for e in x)
        xs_.add(x_)
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
    xs.update(cs)
    return None


def sat_check(xs, target=None, original_xs=None, memory=None, reasons=None, accessed=None):
    global counter
    counter += 1
    if target is None:
        target = ()
    if original_xs is None:
        original_xs = xs
    if memory is None:
        memory = {}
    if reasons is None:
        reasons = {}
    if accessed is None:
        accessed = {}

    def chain(target, col=None):
        nonlocal reasons, original_xs
        if col is None:
            col = []
        if target in original_xs:
            col.append(target)
            return col
        if target in reasons:
            col += list(reasons[target])
        col.append(target)
        return col

    # print(f"target {target}")
    if target in memory:
        # print(f"target {target} found in memory with value {memory[target]}")
        return memory[target]
    value, _, _, xs_ = propagate(set(xs), set(-e for e in target))
    if value is True:
        memory[target] = False
        return False
    if value is False:
        # original_xs.add(target)
        if minimize(original_xs, set(target)) is not None:
            return False
        clean(original_xs)
        memory[target] = True
        return True
    matching = set()
    for x in original_xs:
        if all(e in target for e in x):
            matching.add(x)
            break
    else:
        for x in original_xs:
            if all(e in target for e in x) or \
                any(e in target for e in x) and \
                    not any(-e in target for e in x):
                matching.add(x)
                break
    if matching:
        for x in matching:
            if all(e in target for e in x):
                continue
            x_ = clause(set(x).union(target))
            for e in reversed(list(e for e in x_ if e not in target)):
                x__ = set(x_).difference({e}).union({-e})
                x__ = clause(x__)
                if sat_check(xs_, x__, original_xs=original_xs, memory=memory, reasons=reasons, accessed=accessed):
                    x_ = clause(set(x_).difference({e}))
                else:
                    break
            else:
                continue
            break
        else:
            reasons[target] = matching
            for x in reasons[target]:
                if x not in accessed:
                    accessed[x] = 0
                accessed[x] += 1
            # print(f"Found target {target}; Reason: {reasons[target]}")
            # original_xs.add(target)
            if minimize(original_xs, set(target)) is not None:
                return False
            clean(original_xs)
            memory[target] = True
            return True
    # xs_ = list(x for x in xs if not any(-e in target for e in x))
    # xs_.sort(key=lambda x: tuple(abs(e) for e in x), reverse=False)
    xs__ = list(xs_)
    xs__.sort(key=lambda x: -max(x))
    # xs__.sort(key=lambda x: -sum(abs(e) for e in x))
    vs = None
    if xs__:
        vs = get_variables(xs_)
        vs = {v for v in vs if v > abs(max(target + (0,), key=abs))}
    if vs:
        # v = random.choice(list(vs))
        v = max(vs)
        # x = xs__.pop(0)
        # x = random.choice(xs__)
        # del xs_
        # s = clause(set(target).union(x))
        s = clause(set(target).union({v}))
        if sat_check(xs_, s, original_xs=original_xs, memory=memory, reasons=reasons, accessed=accessed):
            t_ = clause(s)
            for v in (list(clause(set(t_).difference(target)))):
                t = set(t_).difference({v}).union({-v})
                t = clause(t)
                if t not in memory:
                    memory[t] = sat_check(xs_, t, original_xs=original_xs, memory=memory, reasons=reasons, accessed=accessed)
                if memory[t] is False:
                    memory[target] = False
                    return False
                t_ = clause(set(t_).difference({v}))
                if t_ == target:
                    break
            reasons[target] = (t_, s)
            # print(f"Resolved target {target} from clauses {s} and {t}")
            # print(f"With chains:")
            # print(f"\t:{chain(s)}")
            # print(f"\t:{chain(t)}")
            # original_xs.add(target)
            if minimize(original_xs, set(target)) is not None:
                return False
            clean(original_xs)
            memory[target] = True
            return True
    memory[target] = False
    return False


def sat_wrap(xs, targets=None, original_xs=None):
    if not xs:
        return set()
    if not all(xs):
        return None
    vs = get_variables(xs)
    if not sat_check(xs):
        s = set()
        for v in sorted(vs):
            s_ = s.union({v})
            xs_ = exclude(xs, s_)
            if sat_check(preprocess(xs_)):
                s_.remove(v)
                s_.add(-v)
            s = s_
            xs = exclude(xs, s)
        xs = exclude(xs, s)
        if not sat_check(xs):
            return s
    return None


xs = php.php(2, 1)
# xs = php.php(2, 2)
xs = php.php(3, 2)
# xs = php.php(3, 3)
xs = php.php(4, 3)
# xs = php.php(4, 4)
# xs = php.php(5, 4)
# xs = php.php(5, 5)
# xs = php.php(6, 5)
# xs = php.php(6, 6)
counter = 0
accessed = {}
memory = {}
print(sat_check(xs, memory=memory, accessed=accessed), counter)
# with open("examples/factoring2017-0006.dimacs") as file:
# with open("examples/factoring2017-0001.dimacs") as file:
with open("examples/factoring2017.dimacs") as file:
    text = file.read()
    file.close()
    _, xs = dimacs.parse_dimacs(text)
    xs = {clause(set(x)) for x in xs}
    counter = 0
    print(sat_check(xs), counter)
    counter = 0
    print(sat_wrap(xs), counter)
counter = 0
xs = php.php(4, 3)
memory = {}
for x in xs:
    break
print(*(sat_check(xs, target=(-e,), memory=memory) for e in x), counter)


import matplotlib.pyplot as plot

# x = []
# c = []
# y = []

# random.seed(1)
# for (m, n) in [(2, 1), (3, 2), (4, 3), (5, 4), (6, 5), (7, 6), (8, 7), (9, 8), (10, 9), (11, 10)]:
#     xs = php.php(m, n)
#     # xs = randomize(xs)
#     # elem = random.choice(list(xs))
#     # xs.remove(elem)
#     # xs = preprocess(to3(xs))
#     v = len(get_variables(xs))
#     k = len(xs)
#     x.append(v)
#     c.append(k)
#     counter = 0
#     print(sat_check(xs), k, v, counter)
#     # for elem in xs:
#     #     break
#     # print(*(sat_check(xs, target=(-e,), memory=memory) for e in elem), k, v, counter)
#     y.append(counter)

# print(x)
# print(c)
# print(y)
# plot.figure()
# plot.plot(x, y)
# plot.show()
# plot.figure()
# plot.plot(c, y)
# plot.show()

x = []
y = []

random.seed(1)
m = n = 4
xs = php.php(m, n)
index = 1
while True:
    counter = 0
    r = sat_wrap(set(xs))
    print(r, counter)
    if r is not None:
        x.append(len(xs))
        y.append(counter)
        index += 1
        xs.add(clause(-e for e in r))
    else:
        break

print(x)
# y.reverse()
print(y)
plot.figure()
plot.plot(x, y)
plot.show()


# x = []
# y = []

# random.seed(1)
# m = 4
# n = 3
# xs = php.php(m, n)
# index = 1
# for elem in list(xs):
#     counter = 0
#     r = sat_wrap(xs.difference({elem}))
#     print(r, counter)
#     if r is not None:
#         x.append(index)
#         y.append(counter)
#         index += 1
#         xs.add(clause(-e for e in r))
#     else:
#         break

# print(x)
# print(y)
# plot.figure()
# plot.plot(x, y)
# plot.show()
