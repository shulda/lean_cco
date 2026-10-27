#!/usr/bin/env python3
"""Actual finite-packet controls, not certification of infinite CCO or SAP.

Finite domains realize atomic products; domain sizes 3 and 4 distinguish
coordinate growth from stable finite indices in the specified infinite models.
All support lattices below are computed from those actual products.
"""
from itertools import combinations, product


def require(value, message):
    if not value:
        raise AssertionError(message)


def bits(mask):
    while mask:
        bit = mask & -mask
        yield bit.bit_length() - 1
        mask -= bit


class Algebra:
    def __init__(self, points, colour):
        self.points, self.colour = tuple(points), colour
        names = {colour(x, y) for x, y in product(self.points, repeat=2)}
        self.size = len(names)
        require(names == set(range(self.size)), 'contiguous actual atom names')
        self.top = (1 << self.size) - 1
        self.table = [[0] * self.size for _ in names]
        colours = {(x, y): colour(x, y) for x, y in product(self.points, repeat=2)}
        for x, y, z in product(self.points, repeat=3):
            self.table[colours[x, y]][colours[y, z]] |= 1 << colours[x, z]
        self.supports = []
        for candidate in range(1, self.top + 1, 2):
            atoms = tuple(bits(candidate))
            if all(not self.table[a][b] & ~candidate for a in atoms for b in atoms):
                self.supports.append(candidate)
        self.looped = sum(1 << a for a in range(1, self.size) if self.table[a][a] >> a & 1)

    def mul(self, a, b):
        result = 0
        for x in bits(a):
            for y in bits(b):
                result |= self.table[x][y]
        return result

    def generated(self, atoms):
        result = atoms | 1
        while True:
            following = result | self.mul(result, result)
            if following == result:
                return result
            result = following

    def class_at(self, support, point):
        return frozenset(y for y in self.points if support >> self.colour(point, y) & 1)

    def profiles(self):
        words = {1 << a for a in range(self.size)}
        while True:
            following = words | {self.mul(w, 1 << a) for w in words for a in range(self.size)}
            if following == words:
                break
            words = following
        exact = words | {self.top}
        while True:
            following = exact | {a & b for a in exact for b in exact}
            if following == exact:
                return words, exact
            exact = following


def phase_model(r, d, q):
    def colour(x, y):
        coordinates = sum(int(x[i] != y[i]) << i for i in range(r))
        return coordinates | ((x[-1] ^ y[-1]) << r)
    return Algebra((x + (g,) for x in product(range(q), repeat=r) for g in range(1 << d)), colour)


def twin_model(q):
    def colour(x, y):
        if x == y:
            return 0
        if x[:2] == y[:2]:
            return 1
        if x[0] == y[0]:
            return 2
        return 3 if x[1] == y[1] else 4
    return Algebra(product(range(q), range(q), range(2)), colour)


def square_model(q):
    # Each finite four-point fibre is the coloured square: one thin matching
    # (same block), and the nonthin complete bipartite relation between blocks.
    def colour(x, y):
        finite = 0 if x[1:] == y[1:] else (1 if x[1] == y[1] else 2)
        return int(x[0] != y[0]) * 3 + finite
    return Algebra(product(range(q), range(2), range(2)), colour)


def geometry_controls(small, large):
    require(small.table == large.table and small.supports == large.supports,
            'actual products and support lattice stabilize across witness domains')
    supports = small.supports
    sizes = [{s: len(a.class_at(s, a.points[0])) for s in supports} for a in [small, large]]
    indices = {(j, k): (sizes[0][k] // sizes[0][j], sizes[1][k] // sizes[1][j])
               for j, k in product(supports, repeat=2) if j & k == j}
    finite = {pair: values[0] == values[1] for pair, values in indices.items()}
    sigma, kappa = {}, {}
    for j in supports:
        coarsenings = [k for k in supports if (j, k) in finite and finite[j, k]]
        sigma[j] = max(coarsenings, key=int.bit_count)
        require(all(k & sigma[j] == k for k in coarsenings), 'Sigma is greatest finite-index coarsening')
        kappa[j] = small.generated(j & small.looped)
        for k in supports:
            if j & k == j:
                require(finite[j, k] == (small.looped & k & ~j == 0), 'actual relative-index loop criterion')
    packets = {value: {j for j in supports if sigma[j] == value} for value in set(sigma.values())}
    words, exact = small.profiles()
    for j in supports:
        require(finite[kappa[j], j] and sigma[kappa[j]] == sigma[j], 'finite-index exact core')
        require(packets[sigma[j]] == {k for k in supports if kappa[j] & k == kappa[j] and k & sigma[j] == k},
                'canonical packet is the whole closed interval')
        require(kappa[j] == 1 or kappa[j] in words, 'nontrivial core is a positive word profile')
    bottom = sigma[1]
    infinite = [s for s in supports if not finite[1, s]]
    minimal = [e for e in infinite if not any(t != e and t & e == t for t in infinite)]
    crossings = 0
    for e in minimal:
        h = e & bottom
        require(kappa[e] == e and e in exact, 'minimal infinite cut is its exact core')
        require({j for j in supports if j & e == j} == {j for j in supports if j & h == j} | {e},
                'lower interval at a minimal infinite cut')
        for j in supports:
            require(sigma[j] & small.mul(e, j) == small.mul(j, h), 'Sigma crossing intersection')
            for k in supports:
                if (j, k) not in finite or not finite[j, k]:
                    continue
                require(k & small.mul(e, j) == k & small.mul(h, j), 'finite crossing intersection identity')
                left, right = (small.mul(e, j), small.mul(e, k)), (e & j, e & k)
                require(finite[left] and finite[right]
                        and indices[j, k][0] == indices[left][0] * indices[right][0],
                        'actual finite crossing-index product')
                if e & j != e & k:
                    require((e & k) & h == e & k, 'strict crossing refinement stays below finite bottom')
                crossings += 1
    # Actual equivalences commute, not merely their formal lattice labels.
    require(all(small.mul(a, b) == small.mul(b, a) in supports
                for a, b in product(supports, repeat=2)), 'actual represented permutable equivalences')
    return bottom, indices, finite, len(packets), crossings


def regularization_controls(algebra, bottom):
    p = 1
    for atom in bits(bottom & ~1):
        p = algebra.mul(p, algebra.table[atom][atom])
    h0 = p
    while algebra.mul(h0, p) != h0:
        following = algebra.mul(h0, p)
        require(h0 & following == h0, 'regularization powers increase')
        h0 = following
    require(h0 in algebra.supports and h0 & bottom == h0 and algebra.mul(h0, h0) == h0,
            'stabilized finite exact regularization support')
    _, exact = algebra.profiles()
    require(h0 in exact, 'H0 is an actual word-exact equivalence')
    nonthin = any(len(algebra.class_at(1 << a, algebra.points[0])) > 1 for a in bits(bottom))
    require((h0 != 1) == nonthin, 'H0 detects a nonthin finite-bottom atom')
    quotient_classes = {algebra.class_at(h0, x) for x in algebra.points}
    for atom in bits(bottom):
        relation = algebra.mul(h0, 1 << atom)
        require(algebra.mul(relation, relation) == h0, 'finite-bottom quotient orbital squares to identity')
        for cell in quotient_classes:
            x = next(iter(cell))
            targets = {algebra.class_at(h0, y) for y in algebra.points if relation >> algebra.colour(x, y) & 1}
            require(len(targets) == 1, 'actual regularized quotient atom has valency one')
    return h0, nonthin


def thin_group_controls(algebra, r, d, bottom):
    require(bottom == sum(1 << (g << r) for g in range(1 << d)), 'finite bottom is the full phase group')
    subgroups = [mask for mask in range(1, 1 << (1 << d), 2)
                 if all(mask >> (g ^ h) & 1 for g in bits(mask) for h in bits(mask))]
    lifted = {sum(1 << (g << r) for g in bits(h)) for h in subgroups}
    require(lifted == {s for s in algebra.supports if s & bottom == s}, 'entire lower interval is subgroup lattice')
    for g, h in product(range(1 << d), repeat=2):
        require(algebra.table[g << r][h << r] == 1 << ((g ^ h) << r), 'thin translation product is XOR')
    for g in range(1 << d):
        for atom in range(algebra.size):
            require(algebra.table[g << r][atom] == 1 << (atom ^ (g << r)), 'thin translation sends an atom to one atom')
    for x, y in product(algebra.points, repeat=2):
        for g, h in product(range(1 << d), repeat=2):
            tx, ty = x[:-1] + (x[-1] ^ g,), y[:-1] + (y[-1] ^ h,)
            require(algebra.colour(tx, ty) == algebra.colour(x, y) ^ ((g ^ h) << r),
                    'actual two-endpoint thin transport formula')
    if d == 2:
        lines = [s for s in lifted if s.bit_count() == 2]
        a, b, c = lines
        require(a & algebra.mul(b, c) != algebra.mul(a & b, a & c), 'nondistributive F2^2 finite-packet interval')
    return len(subgroups)


def cycles(n):
    # Every undirected simple cycle, with repetitions removed canonically.
    from itertools import permutations
    result = []
    for length in range(3, n + 1):
        for sequence in permutations(range(n), length):
            if sequence[0] == min(sequence) and sequence[1] < sequence[-1]:
                result.append(tuple(tuple(sorted((sequence[i], sequence[(i + 1) % length]))) for i in range(length)))
    return result


def twin_partial_controls(algebra):
    edges = tuple(combinations(range(4), 2))
    edge_index = {e: i for i, e in enumerate(edges)}
    cycle_indices = [tuple(edge_index[e] for e in cycle) for cycle in cycles(4)]
    # Cycle homomorphism existence is computed by actual relational composition.
    cycle_legal = {}
    for length in [3, 4]:
        for word in product(range(1, 5), repeat=length):
            profile = 1
            for atom in word:
                profile = algebra.mul(profile, 1 << atom)
            cycle_legal[word] = bool(profile & 1)
    checked = 0
    for labels in product(range(5), repeat=len(edges)):
        # Zero denotes an unspecified edge, never a prescribed equality edge.
        local = all(cycle_legal[word] for cycle in cycle_indices
                    if all(word := tuple(labels[i] for i in cycle)))
        simultaneous = True
        for coordinate, equal_colours in [(0, {1, 2}), (1, {1, 3})]:
            parent = list(range(4))
            def root(x):
                while parent[x] != x:
                    x = parent[x]
                return x
            for (x, y), atom in zip(edges, labels):
                if atom in equal_colours:
                    parent[root(x)] = root(y)
            simultaneous &= all(root(x) != root(y) for (x, y), atom in zip(edges, labels)
                                if atom and atom not in equal_colours)
        # Independent bipartite solve of the specified t-edge graph.
        adjacency = [[] for _ in range(4)]
        for (x, y), atom in zip(edges, labels):
            if atom == 1:
                adjacency[x].append(y)
                adjacency[y].append(x)
        signs = {}
        for start in range(4):
            if start in signs:
                continue
            signs[start] = 0
            stack = [start]
            while stack:
                x = stack.pop()
                for y in adjacency[x]:
                    if y in signs:
                        simultaneous &= signs[y] != signs[x]
                    else:
                        signs[y] = signs[x] ^ 1
                        stack.append(y)
        require(local == simultaneous, 'twin four-vertex cycle conditions versus independent joint constraint solver')
        checked += 1
    return checked


def run_controls():
    model_count = support_count = packet_count = crossings = 0
    subgroup_counts = {}
    phase_exact = None
    for r, d in [(0, 1), (0, 2), (0, 3), (1, 0), (1, 1), (1, 2), (2, 1), (2, 2)]:
        small, large = phase_model(r, d, 3), phase_model(r, d, 4)
        bottom, indices, finite, packets, crossed = geometry_controls(small, large)
        # Independently classify changed infinite coordinates by bitwise union.
        coordinate_masks = {}
        for support in small.supports:
            mask = 0
            for atom in bits(support):
                mask |= atom & ((1 << r) - 1)
            coordinate_masks[support] = mask
        require(all(finite[j, k] == (coordinate_masks[j] == coordinate_masks[k]) for j, k in indices),
                'finite relative index iff no additional infinite coordinate can change')
        h0, nonthin = regularization_controls(small, bottom)
        require(h0 == 1 and not nonthin, 'fully named phase bottom is already thin')
        subgroup_counts[d] = thin_group_controls(small, r, d, bottom)
        if (r, d) == (2, 1):
            phase_exact = bottom in small.profiles()[1]
        model_count += 1
        support_count += len(small.supports)
        packet_count += packets
        crossings += crossed
    require(subgroup_counts == {0: 1, 1: 2, 2: 5, 3: 16}, 'full small elementary-abelian subgroup counts')
    twin, twin_large = twin_model(3), twin_model(4)
    bottom, _, _, packets, crossed = geometry_controls(twin, twin_large)
    h0, nonthin = regularization_controls(twin, bottom)
    require(bottom == 3 and h0 == 1 and not nonthin, 'twin finite bottom is thin')
    require(twin.table[2][2] & twin.table[3][3] == bottom and bottom in twin.profiles()[1],
            'twin finite bottom is exact as r^2 intersection c^2')
    require(phase_exact is False, 'phase-preserving finite bottom is not exact')
    cells = {twin.class_at(bottom, x) for x in twin.points}
    quotient_atoms = {frozenset((twin.class_at(bottom, x), twin.class_at(bottom, y))
                               for x, y in product(twin.points, repeat=2) if twin.colour(x, y) == atom)
                      for atom in range(twin.size)}
    require(len(cells) == 9 and len(quotient_atoms) - 1 == 3 < twin.size - 1,
            'actual exact twin quotient strictly drops diversity palette')
    diagrams = twin_partial_controls(twin)
    square, square_large = square_model(3), square_model(4)
    square_bottom, _, _, square_packets, square_crossed = geometry_controls(square, square_large)
    square_h0, square_nonthin = regularization_controls(square, square_bottom)
    require(square_nonthin and square_h0 != 1, 'nonthin square fibre has a nonidentity exact regularization')
    print(f'Finite-packet controls passed: {model_count} named-phase products, {support_count} computed supports, '
          f'{packet_count} packets, {crossings} finite crossing intervals; '
          f'F2^d subgroup counts 1/2/5/16 (d=0/1/2/3), including nondistributive F2^2 packets; '
          f'twin: {len(twin.supports)} supports, {packets} packets/{crossed} crossings, '
          f'exact thin F, quotient diversity 4->3, {diagrams} partial diagrams; '
          f'square: {len(square.supports)} supports, {square_packets} packets/{square_crossed} crossings, '
          'nonidentity H0 with actual thin quotient. '
          'No finite snapshot is asserted to certify infinite CCO, SAP, or general theorems.')


def main():
    run_controls()


if __name__ == '__main__':
    main()
