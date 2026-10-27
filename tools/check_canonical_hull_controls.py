#!/usr/bin/env python3
"""Finite controls for actual fibres/hulls; no general theorem certification."""
from itertools import combinations, permutations, product


def require(value, message):
    if not value:
        raise AssertionError(message)


def subsets(values):
    values = tuple(values)
    for n in range(len(values)+1):
        for choice in combinations(values, n):
            yield frozenset(choice)


class Algebra:
    def __init__(self, points, colour):
        self.points, self.colour = tuple(points), colour
        self.names = frozenset(colour(x, y) for x, y in product(self.points, repeat=2))
        self.div = self.names-{0}
        table = {(a, b): set() for a, b in product(self.names, repeat=2)}
        for x, y, z in product(self.points, repeat=3):
            table[colour(x, y), colour(y, z)].add(colour(x, z))
        self.table = {key: frozenset(value) for key, value in table.items()}
        self.squares = {p: self.table[p, p]-{0} for p in self.div}
        self.supports = [r for r in subsets(self.div)
                         if self.mul(r | {0}, r | {0}) <= r | {0}]

    def mul(self, a, b):
        return frozenset().union(*(self.table[x, y] for x, y in product(a, b)))

    def generated(self, values):
        values = frozenset(values) | {0}
        while True:
            following = values | self.mul(values, values)
            if following == values:
                return values-{0}
            values = following

    def intersection(self, family):
        return frozenset.intersection(self.div, *list(family))

    def orbit(self, r, p):
        return self.mul(r | {0}, {p}) & self.div

    def fixed(self, r, p):
        return self.mul(r | {0}, {p}) == {p}

    def class_at(self, r, x):
        return frozenset(y for y in self.points if self.colour(x, y) in r | {0})


def calculus(algebra):
    d, squares = algebra.div, algebra.squares
    h = lambda a, b: algebra.table[a, b] & d
    looped = frozenset(p for p in d if p in squares[p])
    for r in algebra.supports:
        for family in subsets(d):
            intersection = algebra.intersection(squares[p] for p in family)
            if intersection <= r:
                for u, v in product(d, repeat=2):
                    if v not in algebra.orbit(r, u):
                        require(any(not h(p, u) & h(p, v) for p in family), 'R03: separator')
                if all(not algebra.intersection(squares[p] for p in family-{omitted}) <= r
                       for omitted in family):
                    for p in family:
                        if algebra.fixed(r, p):
                            remainder = algebra.intersection(squares[b] for b in family-{p})-r
                            require(all(not squares[a] & remainder for a in squares[p]),
                                    'R03: minimal-blocker square avoidance')
            if not family or not all(algebra.fixed(r, p) for p in family):
                continue
            w = frozenset(a for a in d if squares[a] & intersection <= r)
            require(w in algebra.supports, 'R03: fixed-family pseudocomplement')
            for c in intersection:
                if squares[c] & intersection <= r:
                    require(squares[c] <= r and all(algebra.table[p, c] == {p} for p in family),
                            'R03: spoke-square localisation')
        for u, v, t in product(d, repeat=3):
            if v in algebra.orbit(r, u) and t in h(u, v)-r:
                require(any(z not in r and z in algebra.orbit(r, t) for z in squares[u]),
                        'R03: orbit folding')
    for p, u, v in product(d, repeat=3):
        if u != v:
            require(bool(h(p, u) & h(p, v)) == bool(squares[p] & h(u, v)), 'R03: rectangle')
    for family in subsets(d):
        s = algebra.intersection(squares[p] for p in family)
        generated = algebra.intersection(algebra.generated(squares[p]) for p in family)
        require(not looped & generated or bool(looped & s), 'R03: looped diagonal Helly')
        if family:
            for b in d:
                if looped & s & algebra.generated(squares[b]):
                    require(bool(looped & s & squares[b]), 'R03: carrier insertion')


def cycles(n):
    result = []
    for length in range(3, n+1):
        for sequence in permutations(range(n), length):
            if sequence[0] == min(sequence) and sequence[1] < sequence[-1]:
                result.append(tuple(tuple(sorted((sequence[i], sequence[(i+1) % length])))
                                    for i in range(length)))
    return result


def consistent(n, constraints):
    adjacency = {i: [] for i in range(n)}
    for x, y, gain in constraints:
        adjacency[x].append((y, gain))
        adjacency[y].append((x, gain))
    potential, components = {}, {}
    for start in range(n):
        if start in potential:
            continue
        potential[start], components[start] = 0, start
        stack = [start]
        while stack:
            x = stack.pop()
            for y, gain in adjacency[x]:
                target = potential[x] ^ gain
                if y in potential:
                    if potential[y] != target:
                        return None
                else:
                    potential[y], components[y] = target, start
                    stack.append(y)
    return potential, components


def gain_controls(nested):
    edges = tuple(combinations(range(4), 2))
    simple_cycles = cycles(4)
    cross = 3 if nested else 4
    passed = 0
    for labels in product(range(cross+1), repeat=len(edges)):
        diagram = dict(zip(edges, labels))
        cycle_ok = True
        for cycle in simple_cycles:
            colours = [diagram[e] for e in cycle]
            if 0 in colours:
                continue
            count = colours.count(cross)
            if count:
                legal = count != 1
            elif nested:
                legal = colours.count(2) % 2 == 0 and (2 in colours or len(colours) % 2 == 0)
            else:
                gain = 0
                for c in colours:
                    gain ^= c
                legal = gain == 0
            cycle_ok &= legal
        local = [(x, y, (c == 2) if nested else c)
                 for (x, y), c in diagram.items() if 0 < c < cross]
        solved = consistent(4, local)
        simultaneous = solved is not None
        if solved:
            _, components = solved
            simultaneous &= all(components[x] != components[y]
                                for (x, y), c in diagram.items() if c == cross)
        if nested:
            simultaneous &= consistent(4, [(x, y, 1) for (x, y), c in diagram.items() if c == 1]) is not None
        require(cycle_ok == simultaneous, 'R04: simple cycles versus joint gain solution')
        passed += 1
    return passed


def check():
    packet = Algebra(product(range(3), range(4)),
                     lambda x, y: 4 if x[0] != y[0] else x[1] ^ y[1])
    block = frozenset([1, 2, 3])
    interval = [r for r in packet.supports if r <= block]
    require(len(interval) == 5 and all(frozenset([d]) in interval for d in block), 'R01: M3 interval')
    for a, b in product(interval, repeat=2):
        if a < b and not any(a < c < b for c in interval):
            top_class = packet.class_at(b, (0, 0))
            require(len({packet.class_at(a, x) for x in top_class}) == 2, 'R01: finite packet cover')
    profiles = {frozenset([p]) for p in packet.names} | {packet.names}
    while True:
        following = profiles | {packet.mul(a, b) for a, b in product(profiles, repeat=2)}
        if following == profiles:
            break
        profiles = following
    exact = profiles | {a & b for a, b in product(profiles, repeat=2) if a & b}
    require(block | {0} not in exact and all({0, p} not in exact for p in block),
            'R01: packet and thin connectivity need not be RAW exact')
    c = packet.class_at(block, (0, 0))
    restrict = lambda r: frozenset((x, y) for x, y in product(c, repeat=2)
                                  if packet.colour(x, y) in r | {0})
    require(block != packet.div and restrict(block) == restrict(packet.div),
            'R05: unrestricted lift uniqueness must fail')
    require(len({restrict(r) for r in interval}) == len(interval), 'R05: interval lift uniqueness')

    def nested_colour(x, y):
        if x == y:
            return 0
        if x[0] != y[0]:
            return 3
        return 1 if x[1] == y[1] else 2

    nested = Algebra(product(range(3), range(2), range(2)), nested_colour)
    base_block = tuple(x for x in nested.points if x[0] == 0)
    cardinalities, fibre_cases = {}, 0
    strict_hull_example = False
    for anchors in subsets(base_block):
        if not anchors:
            continue
        for x in set(base_block)-anchors:
            spokes = {a: nested.colour(x, a) for a in anchors}
            p = frozenset(spokes.values())
            z = frozenset(y for y in nested.points if y not in anchors
                          and all(nested.colour(y, a) == b for a, b in spokes.items()))
            t = nested.intersection(nested.squares[b] for b in p)
            fixer = frozenset(d for d in nested.div if all(nested.table[b, d] == {b} for b in p))
            require(t == fixer and fixer in nested.supports and nested.class_at(fixer, x) == z,
                    'R02: finite fibre globalises to spoke-fixer')
            palette = frozenset(nested.colour(y, w) for y, w in product(z, repeat=2) if y != w)
            require(palette == t, 'R02: actual palette equality')
            cardinalities.setdefault(p, set()).add(len(z))
            j = nested.intersection(nested.generated([b]) for b in p)
            hull = frozenset(y for y in nested.points
                             if all(nested.colour(y, a) in nested.generated([b]) | {0}
                                    for a, b in spokes.items()))
            require(hull == nested.class_at(j, x) and z <= hull, 'R02: canonical class and orbit inclusion')
            require(len(hull) & (len(hull)-1) == 0 and len(hull) <= 2**len(j), 'R02: two-power hull bound')
            strict_hull_example |= len(z) == 2 and len(hull) == 4
            fibre_cases += 1
    require(fibre_cases == 28 and strict_hull_example
            and all(len(v) == 1 for v in cardinalities.values()), 'R02: uniformity and strict fibre/hull distinction')

    ultra = Algebra(product(range(3), repeat=3),
                    lambda x, y: next((3-i for i in range(3) if x[i] != y[i]), 0))
    for algebra in [packet, nested, ultra]:
        calculus(algebra)
    gain_cases = gain_controls(False)+gain_controls(True)
    six_edges = tuple(combinations(range(6), 2))
    lookup = {e: i for i, e in enumerate(six_edges)}
    triangles = [tuple(lookup[e] for e in combinations(t, 2)) for t in combinations(range(6), 3)]
    for mask in range(1 << len(six_edges)):
        require(any(((mask >> a) & 1) == ((mask >> b) & 1) == ((mask >> c) & 1)
                    for a, b, c in triangles), 'R05: binary Ramsey K6')
    for k in range(1, 8):
        values = [1]
        for _ in range(k+1):
            values.append(k*values[-1]+1)
        require(all((values[i]-1)//k >= values[i-1] for i in range(1, len(values))),
                'R05: finite Ramsey pivot recurrence')
    print(f'R01–R05 passed: {fibre_cases} actual finite-type cases, {gain_cases} gain diagrams, '
          '32768 binary K6 colourings; fibre/word exactness and hull/orbit boundaries retained. '
          'No general Lean or CCO certification of finite snapshots claimed.')


if __name__ == '__main__':
    check()
