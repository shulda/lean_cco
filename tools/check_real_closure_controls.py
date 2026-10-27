#!/usr/bin/env python3
"""Small mathematical controls for Sections 06--07, not theorem certification.

Three values per infinite coordinate realize its entire binary composition
table. Growing finite domains test fibres, not finite-snapshot algebraicity;
no finite snapshot is asserted to establish infinite CCO, AP, or SAP.
"""
from collections import defaultdict
from itertools import combinations, product
from math import comb


def require(value, message):
    if not value:
        raise AssertionError(message)


def bits(mask):
    while mask:
        bit = mask & -mask
        yield bit.bit_length() - 1
        mask -= bit


def subsets(values, maximum=None):
    values = tuple(values)
    for size in range(min(len(values), maximum if maximum is not None else len(values)) + 1):
        yield from combinations(values, size)


class ProductAlgebra:
    """Actual orbital multiplication from independent finite witness factors."""
    def __init__(self, coordinates, phase=False):
        self.coordinates, self.phase = coordinates, phase
        self.width = coordinates + int(phase)
        self.size = 1 << self.width
        factors = []
        for domain in [range(3)] * coordinates + ([range(2)] if phase else []):
            table = {(a, b): set() for a, b in product(range(2), repeat=2)}
            for x, y, z in product(domain, repeat=3):
                table[int(x != y), int(y != z)].add(int(x != z))
            factors.append(table)
        self.table = []
        for a in range(self.size):
            row = []
            for b in range(self.size):
                outputs = [0]
                for i, factor in enumerate(factors):
                    outputs = [v | (state << i) for v in outputs
                               for state in factor[(a >> i) & 1, (b >> i) & 1]]
                row.append(sum(1 << v for v in outputs))
            self.table.append(row)
        self.top = (1 << self.size) - 1
        self.supports = []
        for candidate in range(1 << (self.size - 1)):
            support = (candidate << 1) | 1
            names = tuple(bits(support))
            if all(not self.table[a][b] & ~support for a in names for b in names):
                self.supports.append(support)

    def multiply(self, left, right):
        result = 0
        for a in bits(left):
            for b in bits(right):
                result |= self.table[a][b]
        return result

    def generated(self, atom):
        support = 1 | (1 << atom)
        while True:
            following = support | self.multiply(support, support)
            if following == support:
                return support
            support = following

    def finite(self, support):
        # In the infinite source, any changed N-coordinate gives an infinite class.
        coordinate_mask = (1 << self.coordinates) - 1
        return all(not atom & coordinate_mask for atom in bits(support))

    def minimal_infinite(self):
        infinite = [s for s in self.supports if not self.finite(s)]
        return [s for s in infinite if not any(t != s and t & s == t for t in infinite)]

    def colour(self, x, y):
        return sum(int(a != b) << i for i, (a, b) in enumerate(zip(x, y)))


def fibres(algebra, anchors, domain):
    classes = defaultdict(set)
    for point in domain:
        classes[tuple(algebra.colour(point, a) for a in anchors)].add(point)
    return classes


def singleton_points(classes):
    return set().union(*(value for value in classes.values() if len(value) == 1))


def coordinate_controls():
    diagonal_cases = base_cases = 0
    for r in range(1, 5):
        algebra = ProductAlgebra(r)
        require(algebra.size - 1 == 2**r - 1, 'coordinate palette size')
        require(len(algebra.supports) == 2**r, 'computed coordinate invariant lattice')
        require(len(algebra.minimal_infinite()) == r, 'computed coordinate minimal directions')
        for atom in range(1, algebra.size):
            expected = sum(1 << b for b in range(algebra.size) if b & atom == b)
            require(algebra.generated(atom) == expected, 'coordinate generated equivalence')
        for n in range(5):
            anchors = tuple((k,) * r for k in range(n))
            small = fibres(algebra, anchors, product(range(n + 2), repeat=r))
            large = fibres(algebra, anchors, product(range(n + 3), repeat=r))
            cube = set(product(range(n), repeat=r))
            require(singleton_points(small) == singleton_points(large) == cube,
                    'diagonal fixed cube from actual spoke fibres')
            require(all(len(large[key]) > len(value) for key, value in small.items()
                        if len(value) > 1), 'nonfixed diagonal fibres grow with fresh values')
            bound = n + sum(comb(n, j) * (2**r - 1)**j for j in range(1, min(r, n) + 1))
            require(len(cube) == n**r <= bound, 'diagonal polynomial binomial bound')
            diagonal_cases += 1
        # Arbitrary small bases, including empty and non-diagonal bases.
        pool = tuple(product(range(2), repeat=r))
        for anchors in subsets(pool, 3 if r <= 3 else 2):
            actual = singleton_points(fibres(algebra, anchors, product(range(4), repeat=r)))
            expected = set(product(*[{a[i] for a in anchors} for i in range(r)]))
            require(actual == expected, 'arbitrary-base coordinate fixed rectangle')
            union = set()
            for small_base in subsets(anchors, r):
                union.update(singleton_points(fibres(algebra, small_base, product(range(4), repeat=r))))
            require(union == actual, 'bounded character from independently computed fibres')
            base_cases += 1
    return diagonal_cases, base_cases


def phase_controls():
    algebra = ProductAlgebra(2, phase=True)
    require(algebra.size - 1 == 7 and len(algebra.supports) == 8,
            'phase palette and full computed support lattice')
    packet = (1 << 0) | (1 << 4)
    finite = [s for s in algebra.supports if algebra.finite(s)]
    origin = (0, 0, 0)
    actual_packet = {x for x in product(range(3), range(3), range(2))
                     if packet >> algebra.colour(origin, x) & 1}
    require(max(finite, key=int.bit_count) == packet
            and actual_packet == {(0, 0, 0), (0, 0, 1)},
            'greatest finite support has actual two-point packets')
    require(len(algebra.minimal_infinite()) == 2, 'phase minimal directions')
    require((algebra.top & ~packet).bit_count() == 6, 'six phase colours outside F')
    for atom in range(1, 8):
        expected = sum(1 << b for b in range(8) if b & atom == b)
        require(algebra.generated(atom) == expected, 'phase generated invariant equivalence')
    # Compute every nonempty atomic-word profile, then every finite intersection.
    words = {1 << atom for atom in range(8)}
    while True:
        following = words | {algebra.multiply(w, 1 << a) for w in words for a in range(8)}
        if following == words:
            break
        words = following
    exact = words | {algebra.top}
    while True:
        following = exact | {a & b for a in exact for b in exact}
        if following == exact:
            break
        exact = following
    require(all(len({a >> 2 for a in bits(w)}) == 1 for w in words), 'word phase parity')
    require(packet not in exact, 'finite packet support is not word-exact')
    require(sum(1 << a for a in [0, 1, 4, 5]) not in exact
            and sum(1 << a for a in [0, 2, 4, 6]) not in exact,
            'phase-forgetting row/column supports are not word-exact')
    a, b, corner = (0, 1, 0), (1, 0, 0), (0, 0, 0)
    small_domain = tuple(product(range(4), range(4), range(2)))
    corner_type = tuple(algebra.colour(corner, anchor) for anchor in [a, b])
    require(fibres(algebra, [a, b], small_domain)[corner_type] == {corner},
            'two corner colours define one point')
    require(corner[:2] not in {a[:2], b[:2]}, 'corner outside F[parameters]')
    require(algebra.generated(algebra.colour(corner, a))
            & algebra.generated(algebra.colour(corner, b)) == 1,
            'corner generated-equivalence meet is identity')
    cases = 0
    for anchors in subsets(tuple(product(range(2), range(2), range(2))), 3):
        first = fibres(algebra, anchors, small_domain)
        larger = fibres(algebra, anchors, product(range(5), range(5), range(2)))
        expected = set(product({a[0] for a in anchors}, {a[1] for a in anchors}, range(2)))
        require(singleton_points(first) == singleton_points(larger) == expected,
                'phase fixed closure contains complete F-packets')
        require(all(len(larger[key]) > len(value) for key, value in first.items()
                    if len(value) > 1), 'nonfixed phase fibres grow')
        n = len(anchors)
        packet_bound = n + sum(comb(n, j) * 6**j for j in range(1, min(2, n) + 1))
        require(len(expected) <= 2 * packet_bound, 'phase polynomial/packet count bound')
        cases += 1
    return cases, len(words), len(exact)


def lattice_controls():
    """All naturally labelled bounded orders through seven elements.

    Every finite lattice admits such a labelling.  Isomorphic repetitions are
    counted separately; these are checks of small lattices, not a general proof.
    """
    lattice_count = monolithic_count = primitive_count = nondistributive = 0
    for n in range(2, 8):
        optional = tuple(combinations(range(1, n - 1), 2))
        for mask in range(1 << len(optional)):
            upper = [(1 << i) | (1 << (n - 1)) for i in range(n)]
            upper[0] = (1 << n) - 1
            for index, (a, b) in enumerate(optional):
                if mask >> index & 1:
                    upper[a] |= 1 << b
            if any(upper[j] & ~upper[i] for i in range(n) for j in bits(upper[i])):
                continue
            lower = [sum(1 << i for i in range(n) if upper[i] >> j & 1) for j in range(n)]
            meet, join = {}, {}
            for a, b in combinations(range(n), 2):
                lows, highs = lower[a] & lower[b], upper[a] & upper[b]
                ms = [i for i in bits(lows) if lows & ~lower[i] == 0]
                js = [i for i in bits(highs) if highs & ~upper[i] == 0]
                if len(ms) != 1 or len(js) != 1:
                    break
                meet[a, b] = meet[b, a] = ms[0]
                join[a, b] = join[b, a] = js[0]
            else:
                for i in range(n):
                    meet[i, i] = join[i, i] = i
                lattice_count += 1
                mis = [j for j in range(n - 1)
                       if all(meet[a, b] != j for a in bits(upper[j] & ~(1 << j))
                              for b in bits(upper[j] & ~(1 << j)))]
                def infimum(values):
                    result = n - 1
                    for value in values:
                        result = meet[result, value]
                    return result
                require(all(infimum(j for j in mis if upper[x] >> j & 1) == x
                            for x in range(n)), 'finite MI separation identity')
                atoms = [i for i in range(1, n) if lower[i] == (1 | (1 << i))]
                if len(atoms) == 1:
                    monolithic_count += 1
                    proper_nonidentity = [j for j in mis if j != 0]
                    require(infimum(proper_nonidentity) == atoms[0], 'unique-atom MI meet')
                    if not proper_nonidentity:
                        require(n == 2 and atoms[0] == n - 1, 'primitive empty MI convention')
                        primitive_count += 1
                    if any(meet[a, join[b, c]] != join[meet[a, b], meet[a, c]]
                           for a, b, c in product(range(n), repeat=3)):
                        nondistributive += 1
    require(primitive_count == 1 and nondistributive > 0, 'primitive and nondistributive coverage')
    return lattice_count, monolithic_count, nondistributive


def coordinate_crt_controls():
    incidence = avoidance = 0
    for r in range(1, 5):
        # A class is a partial coordinate assignment; pairwise compatibility is
        # tested independently against the explicitly enumerated common fibre.
        classes = [(mask, values) for mask in range(1 << r)
                   for values in product(range(2), repeat=mask.bit_count())]
        assignments = [dict(zip(bits(mask), values)) for mask, values in classes]
        points = tuple(product(range(2), repeat=r))
        class_masks = [sum(1 << j for j, x in enumerate(points)
                           if all(x[i] == v for i, v in a.items())) for a in assignments]
        for indices in combinations(range(len(assignments)), 3):
            family = [assignments[i] for i in indices]
            compatible = all(all(a[i] == b[i] for i in a.keys() & b.keys())
                             for a, b in combinations(family, 2))
            witness_mask = class_masks[indices[0]] & class_masks[indices[1]] & class_masks[indices[2]]
            require(bool(witness_mask) == compatible, 'coordinate finite CRT incidence')
            incidence += 1
        for varying in range(1, 1 << r):
            for forbidden_size in range(5):
                forbidden = tuple(tuple((k + i) % (forbidden_size + 1) for i in range(r))
                                  for k in range(forbidden_size))
                # Several arbitrary translates of every lower facet, not just
                # the facets through one origin.  Fresh values avoid all of them.
                facets = [(i, k) for i in bits(varying) for k in range(forbidden_size + 1)]
                fresh = forbidden_size + 1
                witness = tuple(fresh if varying >> i & 1 else 0 for i in range(r))
                require(all(witness[i] != k for i, k in facets)
                        and witness not in forbidden, 'finite translated-facet and point avoidance')
                require(all(witness[i] == 0 for i in range(r) if not varying >> i & 1),
                        'avoidance witness stays in its coordinate class')
                avoidance += 1
    return incidence, avoidance



def terminal_word_controls():
    """F3^2 separates terminal RAW-word equivalences from distributivity.

    This is a finite homogeneous translation model.  No CCO assertion is made;
    its four line equivalences give the nondistributive six-element M4 lattice.
    """
    points = tuple(product(range(3), repeat=2))
    negative = lambda v: tuple((-a) % 3 for a in v)
    representatives = sorted({min(v, negative(v)) for v in points if v != (0, 0)})
    names = {v: i + 1 for i, v in enumerate(representatives)}

    def colour(x, y):
        delta = tuple((b - a) % 3 for a, b in zip(x, y))
        return 0 if delta == (0, 0) else names[min(delta, negative(delta))]

    colours = [[colour(x, y) for y in points] for x in points]
    table = [[0] * 5 for _ in range(5)]
    for x, y, z in product(range(9), repeat=3):
        table[colours[x][y]][colours[y][z]] |= 1 << colours[x][z]

    def multiply(a, b):
        answer = 0
        for i in bits(a):
            for j in bits(b):
                answer |= table[i][j]
        return answer

    supports = [s for s in range(1, 32, 2) if multiply(s, s) & ~s == 0]
    require(len(representatives) == 4 and len(supports) == 6,
            'F3^2 actual four-atom palette and six invariant equivalences')
    classes = {s: frozenset(points[j] for j in range(9) if s >> colours[0][j] & 1)
               for s in supports}
    require(sorted(map(len, classes.values())) == [1, 3, 3, 3, 3, 9],
            'F3^2 computed equivalences are identity, four lines and top')
    for values in classes.values():
        require(all(tuple((a + b) % 3 for a, b in zip(x, y)) in values
                    for x, y in product(values, repeat=2)), 'F3^2 equivalence class is a subspace')
    indices = [len(classes[b]) // len(classes[a]) for a, b in combinations(supports, 2)
               if a & b == a]
    require(set(indices) == {3, 9} and 2 not in indices,
            'full invariant lattice has no relative class index two')

    # Retain literal words, not joins/intersections manufactured as word profiles.
    # The diagonal is an allowed letter; equivalently identity is the empty word.
    profiles = {1 << a: (a,) for a in range(5)}
    frontier = list(profiles)
    while frontier:
        profile = frontier.pop()
        for atom in range(5):
            following = multiply(profile, 1 << atom)
            if following not in profiles:
                profiles[following] = profiles[profile] + (atom,)
                frontier.append(following)
    require(all(s in profiles for s in supports), 'each invariant equivalence is one RAW word profile')
    # Independently compose its actual binary relations on the nine real points.
    for support in supports:
        word = profiles[support]
        for start in range(9):
            endpoints = {start}
            for atom in word:
                endpoints = {z for y in endpoints for z in range(9) if colours[y][z] == atom}
            require(endpoints == {z for z in range(9) if support >> colours[start][z] & 1},
                    'chosen RAW word is the actual full equivalence relation')

    def meet(a, b):
        return a & b

    def join(a, b):
        return min((s for s in supports if (a | b) & s == (a | b)), key=int.bit_count)

    lines = [s for s in supports if len(classes[s]) == 3]
    a, b, c = lines[:3]
    require(meet(a, join(b, c)) != join(meet(a, b), meet(a, c)),
            'terminal full-RAW-word lattice is nondistributive without a CCO hypothesis')

    automorphisms = []
    index = {x: i for i, x in enumerate(points)}
    for translation in points:
        for scalar in [1, 2]:
            permutation = tuple(index[tuple((scalar * a + t) % 3 for a, t in zip(x, translation))]
                                for x in points)
            require(all(colours[x][y] == colours[permutation[x]][permutation[y]]
                        for x, y in product(range(9), repeat=2)), 'translation/scalar automorphism')
            automorphisms.append(permutation)
    # Exhaust all induced partial isometries, even beyond the optional 4-point
    # check: pruning uses only original named colours, never the proposed group.
    partial_maps = 0
    for source in subsets(range(9)):
        def visit(target):
            nonlocal partial_maps
            if len(target) == len(source):
                require(any(all(g[x] == y for x, y in zip(source, target)) for g in automorphisms),
                        'every actual partial isometry extends in the finite F3^2 model')
                partial_maps += 1
                return
            x = source[len(target)]
            for y in range(9):
                if y not in target and all(colours[x][old_x] == colours[y][old_y]
                                           for old_x, old_y in zip(source, target)):
                    visit(target + (y,))
        visit(())
    return len(supports), len(profiles), partial_maps


def run_controls():
    diagonal, bases = coordinate_controls()
    phase, words, exact = phase_controls()
    lattices, monolithic, nondistributive = lattice_controls()
    incidence, avoidance = coordinate_crt_controls()
    terminal_equivalences, terminal_profiles, partial_maps = terminal_word_controls()
    print(f'Real-closure controls passed: {diagonal} diagonal and {bases} arbitrary coordinate bases; '
          f'{phase} phase bases, 8 invariant supports, {words} word/{exact} intersection profiles; '
          f'{lattices} labelled lattices (size 2--7), {monolithic} unique-atom '
          f'({nondistributive} nondistributive); {incidence} CRT triples and {avoidance} avoidance cases; '
          f'F3^2: {terminal_equivalences} equivalences, {terminal_profiles} word profiles, '
          f'{partial_maps} partial isometries, indices 3/9 and nondistributive M4. '
          'Growing-domain fibre controls do not certify infinite CCO/AP/SAP or general theorems.')


def main():
    run_controls()


if __name__ == '__main__':
    main()
