#!/usr/bin/env python3
"""Small represented controls, not an exhaustive audit or proof of CCO.

R01/R02/R04 use the actual F2^2 translation source from ex:exact-ball-sharp.
R03 checks typed algebra only. R05 checks quotient reconstruction only in a
finite grid; that finite grid is NOT claimed to satisfy semantic CCO.
"""
from itertools import combinations, permutations, product


def compose(a, b):
    return frozenset((x, z) for x, y in a for yy, z in b if y == yy)


def converse(r):
    return frozenset((y, x) for x, y in r)


def meet(family, top):
    return frozenset.intersection(top, *family)


def subsets(items):
    for n in range(len(items) + 1):
        yield from combinations(items, n)


def ball(r, centre):
    return frozenset(x for x, y in r if y == centre)


def require(condition, message):
    if not condition:
        raise AssertionError(message)


def check():
    v = tuple(range(4))
    top = frozenset(product(v, repeat=2))
    atoms = [frozenset((x, x ^ d) for x in v) for d in v]
    exact = atoms + [top]
    for a, b in product(exact, repeat=2):
        require(compose(a, b) in exact, 'R01: exact product closure')
    for family in subsets(exact):
        intersection = meet(family, top)
        if all(a & b for a, b in combinations(family, 2)):
            require(bool(intersection), 'R01: exact-menu Helly')
        if intersection:
            for r in exact:
                require(compose(r, intersection) == meet([compose(r, a) for a in family], top),
                        'R01: left nonempty-result distribution')
                require(compose(intersection, r) == meet([compose(a, r) for a in family], top),
                        'R01: right nonempty-result distribution')
    balls = sorted({ball(r, b) for r in exact for b in v}, key=lambda b: (len(b), sorted(b)))
    for family in subsets(balls):
        if all(a & b for a, b in combinations(family, 2)):
            require(bool(meet(family, frozenset(v))), 'R01: exact-ball Helly')

    bad = [atoms[0] | atoms[1], atoms[0] | atoms[2], atoms[1] | atoms[2]]
    bad_balls = [ball(r, 0) for r in bad]
    require(all(a & b for a, b in combinations(bad_balls, 2)) and not meet(bad_balls, frozenset(v)),
            'R02: nonexact invariant ball counterexample must survive')
    require(all(r not in exact for r in bad), 'R02: counterexample menus must be nonexact')
    a, b = atoms[:2]
    require(not (a & b), 'R02: nonempty-indexed meets need not have nonempty result')
    require(compose(compose(top, a & b), top) !=
            compose(compose(top, a), top) & compose(compose(top, b), top),
            'R02: saturation must not preserve an empty intersection')

    # Typed converse orientation. This is an algebra control, not a CCO model.
    sort0, sort1 = [(0, i) for i in range(3)], [(1, i) for i in range(3)]
    d = frozenset((x, y) for x in sort0 for y in sort1 if x[1] == y[1])
    f = frozenset((x, y) for x in sort0 for y in sort0 if x != y)
    for b, c in product(sort1, sort0):
        lhs = bool(ball(d, b) & ball(f, c))
        require(lhs == ((b, c) in compose(converse(d), f)), 'R03: typed ball criterion')
    require(bool(compose(converse(d), f)) and not compose(d, f),
            'R03: omitting the typed converse must be detectable')

    # Three line quotients of F2^2. All cross-sort pair orbits are universal,
    # but independent swaps of these three two-point sorts need not lift.
    coordinates = [lambda x: x & 1, lambda x: (x >> 1) & 1,
                   lambda x: (x & 1) ^ ((x >> 1) & 1)]
    kernels = [frozenset((x, y) for x, y in top if q(x) == q(y)) for q in coordinates]
    require(all(k not in exact for k in kernels), 'R04: line kernels must be nonexact')
    tagged = list(product(range(3), range(2)))

    def act(g, z):
        s, q = z
        return s, q ^ coordinates[s](g)

    def orbital(x, y):
        return frozenset((act(g, x), act(g, y)) for g in v)

    def request(z):
        s, q = z
        return s, q ^ (s == 0)

    require(all(orbital(x, y) == orbital(request(x), request(y)) for x, y in product(tagged, repeat=2)),
            'R04: separate quotient swap must preserve every joint binary orbital')
    require(not any(all(act(g, z) == request(z) for z in tagged) for g in v),
            'R04: nonexact joint request unexpectedly has an ambient lift')

    # A finite grid has nontrivial exact coordinate equivalences. Its orbital
    # algebra tests colour reconstruction, without assuming its ball Helly/CCO.
    grid = list(product(range(3), repeat=2))
    grid_top = frozenset(product(grid, repeat=2))
    grid_atoms = [frozenset((x, y) for x, y in grid_top
                            if (x[0] == y[0], x[1] == y[1]) == flags)
                  for flags in product([False, True], repeat=2)]
    e = frozenset((x, y) for x, y in grid_top if x[0] == y[0])
    h = frozenset((x, y) for x, y in grid_top if x[1] == y[1])
    grid_id = frozenset((x, x) for x in grid)
    e_div, h_div = e - grid_id, h - grid_id
    require(compose(e_div, e_div) == e and compose(h_div, h_div) == h,
            'R05: coordinate equivalences must be represented word profiles')
    for a in grid_atoms:
        e_sat = compose(compose(e, a), e)
        h_sat = compose(compose(h, a), h)
        require(e_sat & h_sat == a, 'R05: fine colour from both exact coordinate quotients')
    require(e & h == grid_id, 'R05: fine kernel must be logical equality')
    for p, q in product(permutations(range(3)), repeat=2):
        for a in grid_atoms:
            moved = frozenset((((p[x[0]], q[x[1]])), ((p[y[0]], q[y[1]]))) for x, y in a)
            require(moved == a, 'R05: original grid atomic orbital invariance')
    return 'R01–R05 passed: exact controls, typed orientation and three false strengthenings; no general proof claimed.'


if __name__ == '__main__':
    print(check())
