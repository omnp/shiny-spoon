
if __name__ == '__main__':
    import random
    import php
    import sat
    import dimacs
    import waerden

    use_dimacs = False
    use_waerden = False

    if not use_dimacs:
        if not use_waerden:
            n = 24
            xs = php.php(n, n)
        else:
            # xs = waerden.waerden(4, 5, 54)  # 55
            xs = waerden.waerden(3, 5, 21)  # 22
            # xs = waerden.waerden(4, 6, 72)  # 73
    else:
        xs = None
        with open("examples/factoring2017-0004.dimacs") as f:
            s = f.read()
            _, xs = dimacs.parse_dimacs(s)
            f.close()
    counter = 0

    def from_from(xs, from_v, limit=None):
        if limit is not None:
            limit -= 1
            if limit <= 0:
                return from_v
        from_from_v = set()
        for fr in from_v:
            t = set()
            for e in fr:
                for x in xs:
                    if -e in x:
                        t = t.union((f for f in x if f != -e))
            t = tuple(sorted(t, key=abs))
            if t and t not in from_v:
                from_from_v.add(t)
        if from_from_v:
            return from_from(xs, from_v.union(from_from_v), limit)
        return from_v.union(from_from_v)

    def minimize(xs, s):
        t = list(sorted(s, key=abs))
        t_ = list(t)
        cs = set()
        for e_ in list(t):
            t = list(t_)
            t.remove(e_)
            while t:
                value, s_, _, _ = sat.propagate(set(xs), set(t))
                if value is True:
                    return s_
                if value is False:
                    c = sat.clause({-e for e in t})
                    for x in list(cs):
                        if all(e in x for e in c):
                            cs.remove(x)
                    cs.add(c)
                    e = random.choice(t)
                    t.remove(e)
                else:
                    break
        xs.update(cs)
        return None

    def rec(xs, s=None, mini=None):
        global counter
        if s is None:
            s = set()
        if mini is None:
            mini = False
        xs_orig = xs
        s_orig = s
        s_list = [(s, 0)]
        while s_list:
            counter += 1
            if s_list:
                s_orig, v = s_list.pop()
            xs = set(xs_orig)
            s = s_orig
            value, s, _, xs = sat.propagate(xs, s)
            print(f"\x1b[2K\rStep {counter}\t | v: {v}", end="")
            if value is False:
                if mini:
                    r = minimize(xs_orig, s_orig)
                    if r is not None:
                        return r
                for t_ in list(s_list):
                    if all(e in t_[0] for e in s_orig):
                        s_list.remove(t_)
                continue
            if not xs:
                assert not any(-e in s for e in s)
                return s
            if not all(xs):
                continue
            vs = sat.get_literals(xs)
            u = v
            v = None
            for e in vs:
                if -e not in vs:
                    if v is None or abs(e) < abs(v) and abs(e) > abs(u):
                        v = e
            if v is None:
                for e in vs:
                    if v is None or abs(e) < abs(v) and abs(e) > abs(u):
                        v = e
            if v is None:
                for e in vs:
                    if -e not in vs:
                        if v is None or abs(e) < abs(v):
                            v = e
                if v is None:
                    for e in vs:
                        if v is None or abs(e) < abs(v):
                            v = e
            vs = [v] + ([] if -v not in vs else [-v])
            xs__ = set(xs)
            s__ = set(s)
            from_v_d = {}
            elems_d = {}
            for v in vs:
                from_v = []
                to_v = []
                xs = set(xs__)
                s = set(s__)
                for x in xs:
                    if -v in x:
                        if x != (-v,):
                            from_v.append(tuple(e for e in x if e != -v))
                    if v in x:
                        if x != (v,):
                            to_v.append(set(-e for e in x if e != v))
                for elems in to_v:
                    elems = tuple(sorted(elems, key=abs))
                    if elems not in elems_d:
                        elems_d[elems] = {}
                    if v not in elems_d[elems]:
                        elems_d[elems][v] = v
                from_from_v = from_from(xs, set(from_v), 2)
                if v not in from_v_d:
                    from_v_d[v] = from_from_v
            for elems in elems_d:
                c = 0
                for v in elems_d[elems]:
                    xs = set(xs__).union(from_v_d[v])
                    s = set(s__).union({v})
                    for x in xs:
                        if len(x) <= 1:
                            s = s.union(set(x))
                    value, s, _, xs = sat.propagate(xs, s)
                    if value is False:
                        c += 1
                        continue
                    if (s, v) not in s_list:
                        s_list.append((s, v))
                if c >= len(elems_d[elems]):
                    if mini:
                        r = minimize(xs_orig, set(elems).union(s__))
                        if r is not None:
                            return r
            for v in vs:
                s = s__.union({v})
                for x in from_v_d[v]:
                    if len(x) <= 1:
                        s = s.union(x)
                if (s, v) not in s_list:
                    s_list.append((s, v))
        return None

    vs = sat.get_variables(xs)
    original_xs = set(xs)
    c = 0
    selected = set()
    while True:
        counter = 0
        xs_ = xs
        r = rec(xs_, mini=True)
        if r is not None:
            r = {e for e in r if abs(e) in vs}
        # print(f"\x1b[2K\r{r}")
        print(r is not None and all(any(e in r for e in x) for x in original_xs))
        print(counter)
        print(len(xs_), len(sat.get_variables(xs_)))
        if r is not None:
            c += 1
            xs.add(tuple(sorted({-e for e in r}, key=abs)))
            # limit = 3
            # t = set()
            # r = r.difference(selected)
            # while limit and r:
            #     e = random.choice(list(r))
            #     r.remove(e)
            #     t.add(-e)
            #     selected.add(e)
            #     limit -= 1
            # t = sat.clause(t)
            # if t not in xs:
            #     xs.add(t)
        else:
            break
    print("Total assignments:", c)
