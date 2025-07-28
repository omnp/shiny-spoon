def check(a, xs, v=None):
    if v is None:
        r = set()
        for x in xs:
            if not any(e in a for e in x):
                r.add(x)
        return r
    else:
        for x in xs:
            if not any(e in a.union({v}) for e in x):
                if -v in x and all(-e in a.union({v}) for e in x):
                    return x
    return []


def solve_(xs, a=None, count=None, trail=None, ovars=None):
    if a is None:
        a = []
        count = [0]
        trail = []
    count[0] += 1
    cs = check(set(a), xs)
    if ovars is not None:
        cs = {c for c in cs if any(abs(e) in ovars for e in c)}
    if not cs:
        assert not any(-e in a for e in a)
        assert all(any(e in a for e in x) for x in clauses)
        return a, count, trail
    c = min(cs, key=len)
    c_ = set(c).difference({-f for f in a})
    for f in c_:
        t = check(set(a), xs, f)
        if not t:
            if not a:
                trail.append(0)
            trail.append(f)
            r = solve_(xs, a + [f], count, trail, ovars=ovars)
            if r[0] is not None:
                return r
    xs.add(tuple(sorted((-e for e in a), key=abs)))
    for x in list(xs):
        for y in xs:
            if x != y and all(e in y for e in x):
                xs.remove(y)
                break
    return None, count, trail


def solve(xs, ovars=None):
    return solve_(set(xs), ovars=ovars)


if __name__ == '__main__':
    # import random
    import php
    import sat
    clauses = php.php(4, 4)
    for _ in range(24):
        print(solve(clauses)[:2])
        clauses = sat.randomize(clauses)
    clauses = php.php(5, 5)
    print(solve(clauses)[1])
    clauses = php.php(6, 6)
    print(solve(clauses)[1])
    clauses = php.php(7, 7)
    print(solve(clauses)[1])
    clauses = php.php(8, 8)
    print(solve(clauses)[1])
    clauses = php.php(9, 9)
    print(solve(clauses)[1])
    k = 19
    clauses = php.php(k, k)
    v = set.union(*(set(abs(e) for e in x) for x in clauses))
    ov = set(v)
    print('Variables:', len(v))
    print('Clauses:', len(clauses))
    c = []
    o = 0
    for i in range(1, len(v)+1, k):
        t = [-(i + j) for j in range(k)]
        t[o] = -t[o]
        # for j in range(len(t)):
        #     h = random.randint(1, len(t))
        #     if random.choice((True, False)):
        #         t.remove(t[h-1])
        c += t
        o += 1
    clauses.add(tuple(c))
    clauses = sat.randomize(clauses)
    clauses = sat.to3(clauses)
    v = set.union(*(set(abs(e) for e in x) for x in clauses))
    print('Variables:', len(v))
    print('Clauses:', len(clauses))
    r = solve(clauses, ovars=ov)
    print(r[1])
    print(r[0] is not None)
