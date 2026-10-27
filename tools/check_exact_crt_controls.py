#!/usr/bin/env python3
"""Finite CRT/order/descent controls; not general mathematical certification."""
from itertools import combinations, product


def require(value, message):
    if not value:
        raise AssertionError(message)


def subsets(values):
    values = tuple(values)
    for n in range(len(values)+1):
        for part in combinations(values, n):
            yield frozenset(part)


def compose(a, b):
    return frozenset((x, z) for x, y in a for yy, z in b if y == yy)


def join(a, b):
    value = a | b
    while True:
        following = value | compose(value, value)
        if following == value:
            return value
        value = following


def partitions(values):
    if not values:
        yield []
        return
    first, *rest = values
    for blocks in partitions(rest):
        yield [frozenset([first])] + blocks
        for i in range(len(blocks)):
            yield blocks[:i] + [blocks[i] | {first}] + blocks[i+1:]


def relation(blocks):
    return frozenset(pair for block in blocks for pair in product(block, repeat=2))


def class_of(e, x):
    return frozenset(y for xx, y in e if xx == x)


def classes(e, vertices):
    return frozenset(class_of(e, x) for x in vertices)


def class_helly(equivalences, vertices):
    blocks = set().union(*(classes(e, vertices) for e in equivalences))
    for family in subsets(blocks):
        if all(a & b for a, b in combinations(family, 2)):
            if not frozenset.intersection(frozenset(vertices), *family):
                return False
    return True


def distributive(equivalences):
    return all(e & join(f, g) == join(e & f, e & g)
               for e, f, g in product(equivalences, repeat=3))


def check():
    vertices = tuple(range(4))
    eqs = [relation(p) for p in partitions(list(vertices))]
    require(len(eqs) == len(set(eqs)) == 15, 'R01: complete four-point equivalence list')
    commuting = 0
    for e, f in product(eqs, repeat=2):
        q = join(e, f)
        image = {(class_of(e, x), class_of(f, x)) for x in vertices}
        compatible = {(a, b) for a, b in product(classes(e, vertices), classes(f, vertices))
                      if (min(a), min(b)) in q}
        permutes = compose(e, f) == compose(f, e)
        require((compatible == image) == permutes, 'R01: two-factor commutation/CRT equivalence')
        if permutes:
            commuting += 1
            require(compose(e, f) == q, 'R01: represented join')
            require(len(image) == len(classes(e & f, vertices)), 'R01: exact coordinate kernel')

    identity = relation([{x} for x in vertices])
    top = frozenset(product(vertices, repeat=2))
    lines = [frozenset((x, y) for x, y in top if x ^ y in {0, d}) for d in [1, 2, 3]]
    boolean = [identity, top]+lines[:2]
    m3 = [identity, top]+lines
    require(distributive(boolean) and class_helly(boolean, vertices), 'R02: Boolean class CRT')
    require(not distributive(m3) and not class_helly(m3, vertices), 'R02: commuting M3 is not enough')
    require(all(compose(a, b) == compose(b, a) for a, b in product(m3, repeat=2)),
            'R02: M3 relations really permute')
    target = tuple(classes(e, vertices) for e in lines)
    require(len(set(product(*target))) == 8
            and len({tuple(class_of(e, x) for e in lines) for x in vertices}) == 4,
            'R02: full M3 tuple deficit')
    three = tuple(range(3))
    e, f = relation([{0, 1}, {2}]), relation([{0}, {1, 2}])
    diamond = [e & f, e, f, join(e, f)]
    require(distributive(diamond) and compose(e, f) != compose(f, e),
            'R02: distributivity alone does not imply commutation')
    require(not class_of(e, 2) & class_of(f, 0) and (2, 0) in join(e, f),
            'R02: distributive nonpermuting compatible pair fails')

    poset_count = 0
    for n in range(5):
        points = frozenset(range(n))
        forward = tuple(combinations(range(n), 2))
        orders = set()
        for chosen in subsets(forward):
            orders.add(join(frozenset((x, x) for x in points), chosen))
        for order in orders:
            poset_count += 1
            lattice = [s for s in subsets(points)
                       if all(y not in s or x in s for x, y in order)]
            irreducibles = [a for a in lattice if a and
                            not any(b < a and c < a and b | c == a
                                    for b, c in product(lattice, repeat=2))]
            phi = lambda a: frozenset(p for p in irreducibles if p <= a)
            psi = lambda d: frozenset().union(*d)
            for a in lattice:
                require(psi(phi(a)) == a, 'R03: join decomposition')
            for downset in subsets(irreducibles):
                if all(not (b in downset and a <= b) or a in downset
                       for a, b in product(irreducibles, repeat=2)):
                    require(phi(psi(downset)) == downset, 'R03: Birkhoff downset inverse')
            mi = [l for l in lattice if l != points and
                  not any(a > l and b > l and a & b == l for a, b in product(lattice, repeat=2))]
            require(all(not a & b <= l or a <= l or b <= l
                        for a, b, l in product(lattice, lattice, mi)), 'R03: meet-prime coordinates')

    carriers = {s: tuple((s, bit) for bit in range(2)) for s in range(3)}
    ids = {s: frozenset((x, x) for x in carriers[s]) for s in carriers}
    tops = {s: frozenset(product(carriers[s], repeat=2)) for s in carriers}

    def atom(s, t, d):
        return frozenset((x, y) for x, y in product(carriers[s], carriers[t]) if x[1] ^ y[1] == d)

    def block(e, a, f):
        return compose(compose(e, a), f)

    a, b = atom(0, 1, 0), atom(1, 2, 0)
    word = compose(a, b)
    projected = compose(block(ids[0], a, tops[1]), block(tops[1], b, ids[2]))
    require(block(ids[0], word, ids[2]) == word and len(word) == 2 and len(projected) == 4,
            'R04: endpoint saturation does not imply factorwise projection')
    require(compose(ids[0], a) != compose(a, tops[1]), 'R04: TI fails in the counterexample')
    # The old endpoint relation remains an atom after quotienting: this does
    # not disprove unrestricted exact descent, only the factorwise identity.
    ti_cases = 0
    for choices in product([False, True], repeat=3):
        kernels = {s: tops[s] if choices[s] else ids[s] for s in carriers}
        for d, h in product(range(2), repeat=2):
            a, b = atom(0, 1, d), atom(1, 2, h)
            left, right = block(kernels[0], a, kernels[1]), block(kernels[1], b, kernels[2])
            qleft = frozenset((class_of(kernels[0], x), class_of(kernels[1], y)) for x, y in left)
            qright = frozenset((class_of(kernels[1], x), class_of(kernels[2], y)) for x, y in right)
            quotient_product = compose(qleft, qright)
            pullback = frozenset((x, y) for x, y in product(carriers[0], carriers[2])
                                 if (class_of(kernels[0], x), class_of(kernels[2], y)) in quotient_product)
            require(pullback == compose(left, right), 'R04: actual quotient product inverse image')
            if (compose(kernels[0], a) == compose(a, kernels[1])
                    and compose(kernels[1], b) == compose(b, kernels[2])):
                ti_cases += 1
                require(compose(left, right) == block(kernels[0], compose(a, b), kernels[2]),
                        'R04: TI word identity')

    j = relation([{0, 1}, {2, 3}])
    q = j | {(0, 2), (2, 0)}
    require(j <= q and compose(compose(j, q), j) != q, 'R05: containment is not general saturation')
    require(j != identity and len(classes(j, vertices)) == 2
            and len(classes(top, vertices)) == 1, 'R05: empty-family ambient Top, not internal top')
    require(frozenset((x, y) for x, y in top if class_of(j, x) == class_of(j, y)) == j,
            'R05: quotient equality pulls back to kernel')
    print(f'R01–R05 passed: 225 equivalence pairs ({commuting} commuting), '
          f'{poset_count} finite posets, {ti_cases} typed TI cases; '
          'set/colour/descent boundaries checked. No general Lean or CCO certification.')


if __name__ == '__main__':
    check()
