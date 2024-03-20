def waerden(j, k, n):
    """
    Implementation following (mainly) the description in 
    The Art of Computer Programming Volume 4 Fascicle 6 (Knuth).
    Read the associated example code also to verify some details.
    """
    xs = set()
    d = 1
    while 1 + (j-1)*d <= n:
        i = 1
        while i + (j-1)*d <= n:
            xs.add(tuple(i+h*d for h in range(j)))
            i += 1
        d += 1
    d = 1
    while 1 + (k-1)*d <= n:
        i = 1
        while i + (k-1)*d <= n:
            xs.add(tuple(-(i+h*d) for h in range(k)))
            i += 1
        d += 1
    return xs