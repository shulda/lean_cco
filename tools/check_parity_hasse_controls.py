#!/usr/bin/env python3
"""Finite algebra/graph controls for parity/Hasse; no general proof or CCO certification."""
from itertools import combinations, product
from math import ceil, comb, exp, log


def require(condition, message):
    if not condition:
        raise AssertionError(message)


def compose(a, b):
    return frozenset((x, z) for x, y in a for yy, z in b if y == yy)


def stable_power(a, unit):
    value = unit
    while True:
        following = compose(value, a)
        require(value <= following, 'Increasing relative powers')
        if following == value:
            return value
        value = following


def colourable(vertices, edges, q):
    adjacency = {v: set() for v in vertices}
    for a, b in edges:
        adjacency[a].add(b)
        adjacency[b].add(a)
    colours = {}

    def search():
        if len(colours) == len(vertices):
            return True
        v = max((v for v in vertices if v not in colours),
                key=lambda w: (len({colours[z] for z in adjacency[w] if z in colours}),
                               len(adjacency[w])))
        forbidden = {colours[z] for z in adjacency[v] if z in colours}
        for d in range(q):
            if d not in forbidden:
                colours[v] = d
                if search():
                    return True
                del colours[v]
        return False

    return search()


def check():
    # All translation-invariant equivalences of F2^3 are its subspaces.
    v = tuple(range(8))
    subspaces = [frozenset(x for x in v if mask & (1 << x)) for mask in range(256)]
    subspaces = [s for s in subspaces if 0 in s and all(x ^ y in s for x, y in product(s, repeat=2))]
    require(len(subspaces) == 16, 'R01: complete F2^3 subspace list')
    join = lambda a, b: frozenset(x ^ y for x, y in product(a, b))
    intervals = 0
    for e, x in product(subspaces, repeat=2):
        f, k = join(e, x), e & x
        require(len(x) // len(k) == len(f) // len(e), 'R01: transposed indices')
        old_classes = {frozenset(z ^ y for z in k) for y in x}
        new_classes = {frozenset(z ^ y for z in e) for y in f}
        image = {frozenset(z ^ min(c) for z in e) for c in old_classes}
        require(image == new_classes and len(image) == len(old_classes), 'R01: actual class bijection')
        if e <= x:
            intervals += 1
            index = len(x) // len(e)
            require(index & (index-1) == 0, 'R01: index is power of two')
            if e < x and not any(e < z < x for z in subspaces):
                require(index == 2, 'R01: full-lattice cover index')
    a, b, c = [frozenset([0, d]) for d in [1, 2, 3]]
    require(a & join(b, c) != join(a & b, a & c), 'R01: retain nondistributive M3')
    for e, f, x in product(subspaces, repeat=3):
        if e <= f:
            require(join(e, x & f) == join(e, x) & f, 'R01: modular identity')

    # Mycielski(C5) is a triangle-free four-chromatic finite obstruction to K3.
    cycle = {tuple(sorted((i, (i+1) % 5))) for i in range(5)}
    edges = set(cycle)
    for a, b in cycle:
        edges.add(tuple(sorted((a, b+5))))
        edges.add(tuple(sorted((b, a+5))))
    edges.update((i+5, 10) for i in range(5))
    require(not any(all(tuple(sorted(e)) in edges for e in combinations(t, 2))
                    for t in combinations(range(11), 3)), 'R02: triangle-free witness')
    require(not colourable(tuple(range(11)), edges, 3) and colourable(tuple(range(11)), edges, 4),
            'R02: high-chromatic witness')
    # Every cycle is length >=4: even ones fold to K3; odd ones have length >=5.
    # Yet the whole graph has no K3 homomorphism. Thus finite K3 is NOT CCO.

    grid = tuple(range(4))
    atoms = [frozenset((x, x ^ d) for x in grid) for d in grid]
    identity, top = atoms[0], frozenset(product(grid, repeat=2))
    left, right = atoms[0] | atoms[1] | atoms[2], atoms[0] | atoms[3]
    require(left & right == identity, 'R03: supports meet at Id')
    require(stable_power(left, identity) & stable_power(right, identity) > identity,
            'R03: nonexact-support separation must fail')
    require(left not in atoms+[top] and right not in atoms+[top], 'R03: supports are nonexact')

    points = tuple(product(range(2), range(3)))
    universe = frozenset(product(points, repeat=2))
    identity = frozenset((x, x) for x in points)
    k = frozenset((x, y) for x, y in universe if x[0] == y[0])
    same, odd = k-identity, universe-k
    exact = {identity, same, odd, k, universe}
    require(all(compose(a, b) in exact for a, b in product(exact, repeat=2)), 'R04: product closure')
    for family in combinations(exact, 3):
        if all(a & b for a, b in combinations(family, 2)):
            require(bool(frozenset.intersection(*family)), 'R04: three-domain support Helly')
    t = compose(compose(k, odd), k)
    require(t == odd and compose(t, t) == k and k | t == universe and not k & t,
            'R04: exact gate equations')
    require(all(sum(1 for a, _ in t if a == x) == 3 for x in points),
            'R04: real relation is NOT a functional graph')
    quotient = {(x[0], y[0]) for x, y in t}
    require(quotient == {(0, 1), (1, 0)}, 'R04: quotient involution')
    require(stable_power(k, k) == k and k != identity, 'R04: nontrivial relative unit')
    # This finite two-sheet structure is an algebra control; do not claim CCO.

    bounds = 0
    for q, r, g in product(range(1, 4), range(1, 4), range(3, 6)):
        c = 128*r*q*log(q+1)
        b = sum(c**ell/(2*ell) for ell in range(3, g+1))
        delta = 8*log(q+1)-log(q)
        n = 2*ceil(max(2*q, c, (q*log(r)+log(4))/delta, 64*r*q*b/c)+1)
        require(delta > 0 and n >= 2*q and n > c and q*log(r)-delta*n < -log(4)
                and c*n/(16*r*q) > 4*b, 'R05: sufficient n inequalities')
        bounds += 1
    for n in range(1, 9):
        for p in [.2, .5, .9]:
            mu = n*p
            prob = sum(comb(n, j)*p**j*(1-p)**(n-j) for j in range(n+1) if j < mu/4)
            require(prob <= exp(-mu/4)+1e-12, 'R05: Bernoulli tail samples')
    for ell in [3, 5, 7]:
        for length in range(ell, 25, 2):
            walk = list(range(ell))+[0]+[z for _ in range((length-ell)//2) for z in [1, 0]]
            require(len(walk) == length+1 and walk[0] == walk[-1]
                    and all((b-a) % ell in [1, ell-1] for a, b in zip(walk, walk[1:])),
                    'R05: odd-cycle padding homomorphism')
    for length in range(4, 26, 2):
        walk = [i % 2 for i in range(length+1)]
        require(walk[0] == walk[-1] and all(a != b for a, b in zip(walk, walk[1:])),
                'R05: even-cycle edge fold')
    print(f'R01–R05 passed: {len(subspaces)} subspaces, {intervals} intervals, '
          f'{bounds} parameter bounds; full-lattice, missing-CCO, nonexact and quotient controls. '
          'No general proof or CCO certification claimed.')


if __name__ == '__main__':
    check()
