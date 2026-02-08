import random
import sys
import php
import sat
import resolution

random.seed(1)
split = False
args = list(sys.argv[1:])
if "split" in args:
    args.remove("split")
    split = True
three = False
if "three" in args:
    args.remove("three")
    three = True
inprocessing = False
if "inprocess" in args:
    args.remove("inprocess")
    inprocessing = True
preprocessing = False
if "preprocess" in args:
    args.remove("preprocess")
    preprocessing = True
randomize = False
if "randomize" in args:
    args.remove("randomize")
    randomize = True
if "seed" in args:
    index = args.index("seed")
    seed = int(args[index + 1])
    random.seed(seed)
    args.pop(index + 1)
    args.pop(index)
if len(args) > 1:
    m, n = args[0:2]
    m, n = int(m), int(n)
    clauses = php.php(m, n)
    print('PHP:{}x{}'.format(m, n))
    variables = sat.get_variables(clauses)
    print(len(clauses), len(variables))
elif len(args) > 0:
    filename = args[0]
    with open(filename) as file:
        import dimacs
        text = file.read()
        variables, clauses = dimacs.parse_dimacs(text)
        clauses = {sat.clause(c) for c in clauses}
        m = len(clauses)
        print(len(clauses), len(variables))
        print('k', max(len(c) for c in clauses))
else:
    import math
    ratio = 4.27
    n = 110
    m = int(math.ceil(n * ratio))
    k = 3
    h = 3  # <= Number of satisfying assignments

    from sat import generate_assignment
    # s = {sat.clause(generate_assignment(n)) for _ in range(h)}
    # _, xs = resolution.random_instance_given_assignments(n, m, k, s)
    # _, xs = resolution.random_instance_given_assignments(n, None, k, s)
    # _, xs = resolution.random_instance_given_assignments(n, None, k, s, clustered=True)
    # _, xs = resolution.random_instance_given_assignments(n, m, k)
    # _, xs = resolution.random_instance_given_assignments(n, None, k)
    _, xs = resolution.random_instance_given_assignments(n, None, k, clustered=True)
    print(len(xs), len(sat.get_variables(xs)))
    clauses = xs
xs = clauses
if randomize:
    xs = sat.randomize(xs)
resolution.counter = 0
total = 0
vs = sat.get_variables(xs)
if three:
    xs = sat.to3(xs)
    print(len(xs), len(sat.get_variables(xs)))
rs_ = []
additional_xs = set()
k = 3

while True:
    counter_ = resolution.counter
    r = resolution.symmetry_breaking(xs, additional_xs, preprocessing=preprocessing, inprocessing=inprocessing)
    if r is not None:
        total += 1
    print("\n\t", r is not None, all(r is None or any(e in r for e in x) for x in xs), resolution.counter - counter_, total)
    if r is None:
        break
    r = sat.clause(-e for e in r if abs(e) in vs)
    if split:
        r = list(r)
        random.shuffle(r)
        r = sat.clause(r[:k])
    for x in xs.union(additional_xs):
        y = sat.resolve(r, x)
        if y is not None and len(y) < len(r):
            if y not in xs.union(additional_xs):
                r = y
    xs.add(r)
    if r not in rs_:
        rs_.append(r)
