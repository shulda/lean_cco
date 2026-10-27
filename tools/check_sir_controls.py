#!/usr/bin/env python3
"""Finite SIR controls; no claim to prove an infinite-source theorem.

Five-point snapshots check every finite-set overlap and every prescribed
partial isomorphism. Existence is tested through selected finite amalgams,
not by pretending a bounded snapshot contains all needed fresh copies.
"""
from itertools import combinations, permutations, product


def require(condition, message):
    if not condition:
        raise AssertionError(message)


def members(mask, n):
    return [i for i in range(n) if mask & (1 << i)]


def submasks(mask):
    sub = mask
    while True:
        yield sub
        if not sub:
            break
        sub = (sub-1) & mask


def finite_relation_check(n, colour, independent):
    size = 1 << n
    table = [[[independent(a, b, c) for b in range(size)]
              for a in range(size)] for c in range(size)]
    for c, a, b in product(range(size), repeat=3):
        value = table[c][a][b]
        require(value == table[c][b][a], 'Symmetry')
        require(value == table[c][a | c][b | c], 'Base normalization')
        if value:
            for smaller in submasks(a):
                require(table[c][smaller][b], 'Restriction monotonicity')
        for d in range(size):
            require(table[c][a][b | d] == (value and table[b | c][a][d]),
                    'Both transitivity directions with arbitrary overlaps')
    stationary = 0
    empty_base = 0
    # Every injective finite map; only induced isomorphisms are relevant.
    for domain in range(size):
        points = members(domain, n)
        for targets in permutations(range(n), len(points)):
            mapping = dict(zip(points, targets))
            if any(colour(i, j) != colour(mapping[i], mapping[j])
                   for i, j in combinations(points, 2)):
                continue
            image = sum(1 << i for i in targets)
            fixed = sum(1 << i for i in points if mapping[i] == i)
            for c in submasks(fixed):
                for b in range(size):
                    if not (table[c][domain][b] and table[c][image][b]):
                        continue
                    union = {i: i for i in members(b | c, n)}
                    require(all(i not in union or union[i] == j for i, j in mapping.items()),
                            'Prescribed map well-defined on union')
                    union.update(mapping)
                    require(len(set(union.values())) == len(union), 'Prescribed map injective')
                    require(all(colour(i, j) == colour(union[i], union[j])
                                for i, j in combinations(union, 2)),
                            'Pointwise stationarity of prescribed map')
                    stationary += 1
                    empty_base += c == 0
    require(empty_base > 0, 'Empty-base stationarity cases must be exercised')
    return stationary, empty_base


def check():
    n = 5
    top = frozenset({1, 2, 3})

    def ultra_colour(a, b):
        if a == b:
            return 0
        if a == 4 or b == 4:
            return 3
        return 1 if a // 2 == b // 2 else 2

    def atom_product(a, b):
        return frozenset(range(1, a+1)) if a == b else frozenset({max(a, b)})

    def menu(base, a, b):
        require(a != b and not base & ((1 << a) | (1 << b)), 'Strong endpoint guard')
        result = top
        for c in members(base, n):
            result &= atom_product(ultra_colour(a, c), ultra_colour(c, b))
        return result

    def selected_independent(a, b, c):
        if (a & b) & ~c:
            return False
        return all(ultra_colour(x, y) == max(menu(c, x, y))
                   for x in members(a & ~c, n) for y in members(b & ~c, n))

    positive_stats = finite_relation_check(n, ultra_colour, selected_independent)
    amalgams = 0
    # Per vertex: absent / base / left-only / right-only.
    for roles in product(range(4), repeat=n):
        c = sum(1 << i for i, role in enumerate(roles) if role == 1)
        a = c | sum(1 << i for i, role in enumerate(roles) if role == 2)
        b = c | sum(1 << i for i, role in enumerate(roles) if role == 3)
        points = members(a | b, n)

        def new_colour(x, y):
            old_pair = ((a >> x) & (a >> y) & 1) or ((b >> x) & (b >> y) & 1)
            return ultra_colour(x, y) if old_pair else max(menu(c, x, y))

        for x, y, z in combinations(points, 3):
            colours = [new_colour(x, y), new_colour(x, z), new_colour(y, z)]
            require(colours.count(max(colours)) >= 2, 'Selected amalgam is triangle-legal')
        amalgams += 1

    # Direct relative example: no selector or NR2 assumption is used.
    points = [(0, 0, 0), (0, 0, 1), (0, 1, 0), (1, 0, 0), (1, 1, 0)]

    def sheet_colour(a, b):
        if a == b:
            return 0
        x, y = points[a], points[b]
        return 3 if x[0] != y[0] else 1 if x[1] == y[1] else 2

    parents = [sum(1 << i for i, point in enumerate(points) if point[0] == parent)
               for parent in [0, 1]]

    def parent_independent(a, b, c):
        return not ((a & b) & ~c) and all((p & c) or not (p & a and p & b) for p in parents)

    relative_stats = finite_relation_check(n, sheet_colour, parent_independent)
    # Two sheets determine the BOTH FALSE case; three sheets do not.
    three = [(0, 0), (1, 0), (2, 0), (1, 1)]
    e = lambda x, y: three[x][0] == three[y][0]
    require(not e(1, 0) and not e(2, 0) and not e(3, 0) and e(1, 3) != e(2, 3),
            'Direct relation cannot silently allow three sheets per anchored parent')

    # Naturality cannot cover a nonsurjective map to a larger target base.
    selected_empty = max(top)
    selected_larger = max(atom_product(1, 1))
    require(selected_empty == 3 and selected_larger == 1,
            'Onto-base naturality firewall')

    # Global two-class swap: setwise B preservation is not pointwise typing.
    global_points = [(sheet, fibre) for sheet in [0, 1] for fibre in [0, 1]]
    parameter_pair = {0, 2}
    swap = lambda i: i ^ 2
    require({swap(i) for i in parameter_pair} == parameter_pair, 'Setwise pair preservation')
    for x in range(4):
        first = tuple(global_points[x][0] == global_points[b][0] for b in [0, 2])
        moved = tuple(global_points[swap(x)][0] == global_points[b][0] for b in [0, 2])
        require(first != moved, 'Pointwise E-types must distinguish swapped sheets')
    return (f'R01–R05 passed: {amalgams} selected spans; all 5-point set overlaps in both models; '
            f'{positive_stats[0]}/{relative_stats[0]} prescribed-map stationarity cases '
            f'({positive_stats[1]}/{relative_stats[1]} over empty base). No general proof claimed.')


if __name__ == '__main__':
    print(check())
