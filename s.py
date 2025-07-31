
if __name__ == '__main__':
    import php
    import sat
    import dimacs
    import waerden

    use_dimacs = False
    use_waerden = False

    if not use_dimacs:
        if not use_waerden:
            # n = 128
            n = 24
            xs = php.php(n, n)
            # xs = php.php(n, 2*n)
            # xs = {(1, 2, 3), (-2, -3, 4), (-1, 3, -4)}
            # xs = sat.randomize(xs)
        else:
            # xs = waerden.waerden(4, 5, 55)
            # xs = waerden.waerden(4, 5, 54)
            xs = waerden.waerden(3, 5, 22)
    else:
        xs = None
        with open("examples/factoring2017-0004.dimacs") as f:
            s = f.read()
            _, xs = dimacs.parse_dimacs(s)
            f.close()
    counter = 0

    def rec(xs, s=None):
        global counter
        if s is None:
            s = set()
        xs_orig = xs
        s_orig = s
        s_list = [(s, 0)]
        s_all = [s]
        while s_list:
            counter += 1
            s_orig, v = s_list.pop()
            xs = set(xs_orig)
            s = s_orig
            value, s, _, xs = sat.propagate(xs, s)
            print(f"\x1b[2K\rStep {counter}\t | v: {v}", end="")
            if not xs:
                assert not any(-e in s for e in s)
                return s
            if not all(xs):
                continue
            vs = sat.get_literals(xs)
            v = None
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
            for v in vs:
                from_v = []
                to_v = []
                xs = set(xs__)
                for x in xs:
                    if -v in x:
                        if x != (-v,):
                            from_v.append(tuple(e for e in x if e != -v))
                    if v in x:
                        if x != (v,):
                            to_v.append(set(-e for e in x if e != v))
                # print("v", v)
                # print("from_v", from_v)
                # print("to_v", to_v)
                if to_v:
                    for elems in reversed(to_v):
                        xs_ = set(xs__).union(from_v)
                        s_ = set(s__).union({v})
                        xs = xs_
                        from_from_v = set()
                        for fr in from_v:
                            t = set()
                            for e in fr:
                                for x in xs:
                                    if -e in x:
                                        t = t.union((f for f in x if f != -e))
                            if t:
                                from_from_v.add(tuple(sorted(t, key=abs)))
                        to_to_v = set()
                        for e in elems:
                            t = set()
                            for x in xs:
                                if e in x:
                                    t = t.union((-f for f in x if f != e))
                            if t:
                                to_to_v.add(tuple(sorted(t, key=abs)))
                        # print("elems", elems)
                        # print("from_from_v", from_from_v)
                        # print("to_to_v", to_to_v)
                        xs = xs_.union({(e,) for e in elems}).union(from_from_v).union(to_to_v)
                        s = set(s_)
                        for x in xs:
                            if len(x) <= 1:
                                s = s.union(set(x))
                        s = s.union(elems)
                        value, s, _, xs = sat.propagate(xs, s)
                        if value is False:
                            continue
                        del xs_
                        del xs
                        if s not in s_all:
                            s_list.append((s, v))
                            s_all.append(s)
                else:
                    xs = set(xs__).union(from_v)
                    s = set(s__).union({v})
                    for x in xs:
                        if len(x) <= 1:
                            s = s.union(set(x))
                    value, s, _, xs = sat.propagate(xs, s)
                    if value is False:
                        continue
                    del xs
                    if s not in s_all:
                        s_list.append((s, v))
                        s_all.append(s)
        return None

    vs = sat.get_variables(xs)
    while True:
        counter = 0
        xs_ = sat.to3(xs)
        r = rec(set(xs_))
        if r is not None:
            r = {e for e in r if abs(e) in vs}
        print(f"\x1b[2K\r{r}")
        print(r is not None and all(any(e in r for e in x) for x in xs))
        print(counter)
        print(len(xs_), len(sat.get_variables(xs_)))
        if r is not None:
            xs.add(tuple(sorted({-e for e in r}, key=abs)))
        else:
            break
