def quadratic_twists(E, B):
    """
    Return iterator over all pairs `(d, E^d)`, where the `E^d` run
    over all quadratic twists of `E` with norm conductor at most `B`.

    INPUT:

    - E -- an elliptic curve over F=Q(sqrt(5))
    - B -- positive integer

    AUTHOR: William Stein
    """
    N = E.conductor()
    F = E.base_field()
    P1 = prime_divisors(N)
    v = [p for p, e in N.factor() if e==1]
    if len(v) == 0:
        C = 1
    else:
        C = prod(v).norm()
    B2 = int(sqrt(B/C))
    P2 = [(p, p.norm()) for p in sum([F.primes_above(p) for p in primes(B2+1)],[]) if p.norm() <= B2] 
    for s in [-1,1]:
        for eps in [0,1]:
            for Z in subsets(P1):
                d1 = prod(Z).gens_reduced()[0] if Z else F(1)
                for W in subsets(P2):
                    if prod(n for _, n in W) <= B2:
                        d2 = prod([p for p,_ in W]).gens_reduced()[0] if W else F(1)
                        d = d2*d1*s*F.gen()^eps
                        if d != 1:
                            Ed = E.quadratic_twist(d).global_minimal_model()
                            if Ed.conductor().norm() <= B:
                                yield Ed, d
