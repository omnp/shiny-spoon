def php(m, n):
    """Pigeon hole principle."""
    k = m*n
    vs = set(range(1,k+1))
    xs = set()
    for i in range(1,k+1, n):
        x = tuple(range(i,i+n))
        xs.add(x)
    xs_ = set(xs)
    for x in xs_:
        for y in xs_:
             if x != y:
                 for e,f in zip(x,y):
                     xs.add(tuple(sorted((-e,-f,),key=abs)))
    return xs
