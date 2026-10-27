#!/usr/bin/env python3
"""Actual finite binary-fibre kernels and finite linear projection controls.

Canonical orbit structures are computed as literal unary/binary relations;
automorphisms and local motions are independently enumerated permutations.
Finite exhaustion does not certify countable compactness, CCO, or exactness.
"""
from functools import lru_cache
from itertools import combinations, permutations, product


def require(value, message):
    if not value:
        raise AssertionError(message)


def subsets(values):
    values = tuple(values)
    for size in range(len(values) + 1):
        yield from combinations(values, size)


def dot(a, b):
    return (a & b).bit_count() & 1


class BinaryStructure:
    def __init__(self, fibres, action, named=True):
        self.fibres = tuple(tuple(c) for c in fibres)
        self.n = sum(map(len, fibres))
        self.owner = {x: i for i, c in enumerate(fibres) for x in c}
        self.unary = tuple(self.owner[x] if named else 0 for x in range(self.n))
        self.colour = [[min(g[x] * self.n + g[y] for g in action)
                        for y in range(self.n)] for x in range(self.n)]
        self.named = named

    def preserves(self, mapping):
        return all(self.unary[x] == self.unary[y] for x, y in mapping.items()) and all(
            self.colour[x][y] == self.colour[mapping[x]][mapping[y]] for x, y in product(mapping, repeat=2))

    def automorphisms(self):
        candidates = product(*(permutations(c) for c in self.fibres)) if self.named else None
        if candidates is None:
            return [p for p in permutations(range(self.n)) if self.preserves(dict(enumerate(p)))]
        return [tuple(y for c in candidate for y in c) for candidate in candidates
                if self.preserves({x: y for c, image in zip(self.fibres, candidate) for x, y in zip(c, image)})]

    def intrinsic(self):
        return [[p for p in permutations(c) if self.preserves(dict(zip(c, p)))] for c in self.fibres]

    def local_pairs(self, intrinsic):
        return {(i, j): {(a, b) for a, b in product(intrinsic[i], intrinsic[j])
                         if self.preserves(dict(zip(self.fibres[i] + self.fibres[j], a + b)))}
                for i, j in combinations(range(len(self.fibres)), 2)}

    def owner_kernel(self, automorphisms):
        return [g for g in automorphisms if all(self.owner[g[x]] == self.owner[x] for x in range(self.n))]

    def motions(self, kernel):
        return {tuple(tuple(g[x] for x in c) for c in self.fibres) for g in kernel}

    def all_partial_isometries(self, automorphisms):
        count = 0
        for domain in subsets(range(self.n)):
            def extend(image):
                nonlocal count
                if len(image) == len(domain):
                    require(any(all(g[x] == y for x, y in zip(domain, image)) for g in automorphisms),
                            'actual finite partial isometry extends')
                    count += 1
                    return
                x = domain[len(image)]
                for y in range(self.n):
                    if y not in image and self.unary[x] == self.unary[y]:
                        mapping = dict(zip(domain[:len(image) + 1], image + (y,)))
                        if self.preserves(mapping):
                            extend(image + (y,))
            extend(())
        return count


def kernel_controls(structure):
    aut = structure.automorphisms()
    require(all(len({structure.owner[g[x]] for x in c}) == 1
                for g in aut for c in structure.fibres), 'the entire finite-class partition is actually invariant')
    intrinsic = structure.intrinsic()
    pairs = structure.local_pairs(intrinsic)
    actual = structure.motions(structure.owner_kernel(aut))
    indices = tuple(range(len(intrinsic)))
    solutions, projections = {}, {}
    for chosen in subsets(indices):
        solutions[chosen] = {values for values in product(*(intrinsic[i] for i in chosen))
                             if all((values[a], values[b]) in pairs[i, j]
                                    for a, i in enumerate(chosen) for b, j in enumerate(chosen) if a < b)}
        projections[chosen] = {tuple(g[i] for i in chosen) for g in actual}
    require(solutions[indices] == actual, 'actual binary local motions patch to the owner kernel')
    bindings = [{g[i] for g in actual} for i in indices]
    actual_pairs = {(i, j): {(g[i], g[j]) for g in actual} for i, j in combinations(indices, 2)}
    pair_join = {g for g in product(*bindings)
                 if all((g[i], g[j]) in actual_pairs[i, j] for i, j in actual_pairs)}
    require(pair_join == actual, 'actual binding and pair images recover the full kernel')
    require(all({a for a, _ in p} == bindings[i] and {b for _, b in p} == bindings[j]
                for (i, j), p in actual_pairs.items()), 'actual pairs are subdirect over actual bindings')
    candidates = blocked = 0
    for chosen in subsets(indices):
        supersets = [t for t in subsets(indices) if set(chosen) <= set(t)]
        for value in product(*(intrinsic[i] for i in chosen)):
            def extends_at(t):
                positions = [t.index(i) for i in chosen]
                return any(tuple(h[k] for k in positions) == value for h in solutions[t])
            all_levels = all(extends_at(t) for t in supersets)
            require((value in projections[chosen]) == all_levels,
                    'finite exhaustion extension criterion, including empty S')
            exhaustion = [tuple(sorted(set(chosen) | set(indices[:level]))) for level in range(len(indices) + 1)]
            require(all_levels == all(extends_at(t) for t in exhaustion), 'nested finite exhaustion detects obstruction')
            if value not in projections[chosen]:
                require(any(not extends_at(t) for t in supersets), 'nonextendible motion fails an actual finite level')
                blocked += 1
            candidates += 1
    return aut, intrinsic, pairs, actual, solutions, projections, bindings, actual_pairs, candidates, blocked


def hidden_parity_model():
    fibres = [(0, 1), (2, 3), (4, 5), (6, 7, 8, 9)]
    action = []
    for u, v in product(range(2), repeat=2):
        action.append(tuple([x ^ u for x in range(2)] + [2 + (x ^ v) for x in range(2)]
                            + [4 + (x ^ u ^ v) for x in range(2)]
                            + [6 + (x ^ (u | (v << 1))) for x in range(4)]))
    structure = BinaryStructure(fibres, action)
    data = kernel_controls(structure)
    aut, intrinsic, pairs, actual, solutions, projections, bindings, actual_pairs, candidates, blocked = data
    require(len(aut) == 4 and sorted(aut) == sorted(action), 'actual full named-fibre automorphism group is exactly four shifts')
    require(list(map(len, intrinsic)) == [2, 2, 2, 4], 'actual intrinsic groups C2,C2,C2,F2^2')
    require(all(len(p) == 4 for p in pairs.values()), 'actual six local pair groups')
    require(len(solutions[0, 1, 2]) == 8 and len(projections[0, 1, 2]) == 4,
            'ABC local pair join is unrestricted but actual triple projection has size four')
    require(all(actual_pairs[i, j] == set(product(bindings[i], bindings[j])) for i, j in combinations(range(3), 2)),
            'all actual two-coordinate marginals on ABC are unrestricted')
    witness = (intrinsic[0][1], intrinsic[1][0], intrinsic[2][0])
    mapping = dict(zip(fibres[0] + fibres[1] + fibres[2], sum(witness, ())))
    require(structure.preserves(mapping) and not any(all(g[x] == y for x, y in mapping.items()) for g in aut),
            'triple flip is an actual nonextendible finite partial binary isomorphism')
    require(witness in solutions[0, 1, 2] and witness not in projections[0, 1, 2], 'hidden parity obstruction survives pair checks')
    def code_motion(i, motion):
        return motion[0] - fibres[i][0]
    actual_codes = {sum(code_motion(i, g[i]) << [0, 1, 2, 3][i] for i in range(4)) for g in actual}
    require(actual_codes == {u | (v << 1) | ((u ^ v) << 2) | (u << 3) | (v << 4)
                             for u, v in product(range(2), repeat=2)}, 'actual ABC projection is a+b+c=0')
    pair_rows = []
    masks = block_masks((1, 1, 1, 2))
    for (i, j), local in pairs.items():
        motions = {code_motion(i, a) << [0, 1, 2, 3][i] | code_motion(j, b) << [0, 1, 2, 3][j]
                   for a, b in local}
        pair_rows.extend(row for row in range(32) if row & ~(masks[i] | masks[j]) == 0
                         and all(not dot(row, value) for value in motions))
    failures, tests = linear_projection_controls((1, 1, 1, 2), pair_rows, expected=actual_codes)
    require(failures == {(0, 1, 2)}, 'only ABC develops a width-three projected parity row')
    return candidates, blocked, tests


def moving_owner_model():
    elements = tuple(permutations(range(3)))
    index = {p: i for i, p in enumerate(elements)}
    def mul(p, q):
        return tuple(p[q[i]] for i in range(3))
    identity, swap = (0, 1, 2), (1, 0, 2)
    action = [tuple(index[mul(g, x)] for x in elements) for g in elements]
    cosets = sorted({tuple(sorted(index[mul(g, h)] for h in [identity, swap])) for g in elements})
    structure = BinaryStructure(cosets, action, named=False)
    data = kernel_controls(structure)
    aut, intrinsic, pairs, actual, solutions, projections, bindings, actual_pairs, candidates, blocked = data
    require(len(aut) == 6 and sorted(aut) == sorted(action), 'actual unnamed-owner regular S3 automorphism group')
    require(len(actual) == 1 and list(map(len, intrinsic)) == [2, 2, 2] and list(map(len, bindings)) == [1, 1, 1],
            'genuine moving-owner model has strict B_C < H_C')
    require(all(len(p) == 1 for p in pairs.values()), 'actual local pair groups need not be subdirect over intrinsic groups')
    require(len({tuple(structure.owner[g[c[0]]] for c in structure.fibres) for g in aut}) == 6,
            'unnamed finite owners genuinely move and their action is faithful')
    partials = structure.all_partial_isometries(aut)
    # The original canonical structure is homogeneous; naming all owners breaks
    # this property, as a flip within one whole two-point owner cannot extend N.
    flip = dict(zip(cosets[0], reversed(cosets[0])))
    require(structure.preserves(flip) and not any(all(g[i] == y for i, y in flip.items())
                                                for g in structure.owner_kernel(aut)), 'owner-named expansion fails relative homogeneity')
    return candidates, blocked, partials


def entire_named_sort_model():
    action = [(0, 1, 2, 3), (1, 0, 3, 2)]
    structure = BinaryStructure([(0, 1), (2, 3)], action)
    data = kernel_controls(structure)
    aut, intrinsic, pairs, actual, solutions, projections = data[:6]
    require(all(solutions[s] == projections[s] for s in solutions), 'strong entire-named-sort projection in an actual homogeneous model')
    partials = structure.all_partial_isometries(aut)
    return len(solutions), partials


def gaussian_basis(rows):
    basis = {}
    for row in rows:
        for pivot in sorted(basis, reverse=True):
            if row >> pivot & 1:
                row ^= basis[pivot]
        if row:
            pivot = row.bit_length() - 1
            for other in basis:
                if basis[other] >> pivot & 1:
                    basis[other] ^= row
            basis[pivot] = row
    return tuple(basis[p] for p in sorted(basis, reverse=True))


def span(rows):
    values = {0}
    for row in gaussian_basis(rows):
        values |= {value ^ row for value in values}
    return frozenset(values)


def gaussian_kernel(rows, n):
    basis = gaussian_basis(rows)
    pivots = {row.bit_length() - 1 for row in basis}
    generators = []
    for free in range(n):
        if free not in pivots:
            value = 1 << free
            for row in basis:
                if row >> free & 1:
                    value |= 1 << (row.bit_length() - 1)
            generators.append(value)
    return span(generators)


def block_masks(dimensions):
    result, offset = [], 0
    for dimension in dimensions:
        result.append(((1 << dimension) - 1) << offset)
        offset += dimension
    return result


def linear_projection_controls(dimensions, rows, expected=None):
    n = sum(dimensions)
    masks = block_masks(dimensions)
    relation_rows = span(rows)
    enumeration = {value for value in range(1 << n) if all(not dot(row, value) for row in rows)}
    require(enumeration == gaussian_kernel(rows, n), 'independent tuple enumeration versus Gaussian nullspace')
    if expected is not None:
        require(enumeration == expected, 'local-pair Gaussian kernel equals actual binary automorphisms')
    projections, supported_rows = {}, {}
    indices = tuple(range(len(dimensions)))
    for chosen in subsets(indices):
        mask = sum(masks[i] for i in chosen)
        projections[chosen] = {value & mask for value in enumeration}
        supported_rows[chosen] = {row for row in relation_rows if row & ~mask == 0}
        annihilator = {row for row in range(1 << n) if row & ~mask == 0
                       and all(not dot(row, value) for value in projections[chosen])}
        require(annihilator == supported_rows[chosen], 'Ann(actual finite projection) equals R intersect D_S')
    failures = set()
    for chosen in subsets(indices):
        mask = sum(masks[i] for i in chosen)
        small = [t for t in subsets(chosen) if len(t) <= 2]
        generated = span(row for t in small for row in supported_rows[t])
        pair_join = {value for value in range(1 << n) if value & ~mask == 0
                     and all(value & sum(masks[i] for i in t) in projections[t] for t in small)}
        width_two = generated == supported_rows[chosen]
        require(width_two == (pair_join == projections[chosen]), 'width-two dual criterion iff actual marginal pair join')
        if not width_two:
            failures.add(chosen)
    return failures, 1 << len(dimensions)


@lru_cache(maxsize=None)
def all_rowspaces(n):
    spaces = {frozenset([0])}
    frontier = list(spaces)
    while frontier:
        old = frontier.pop()
        for value in range(1 << n):
            if value not in old:
                new = old | {x ^ value for x in old}
                if new not in spaces:
                    spaces.add(new)
                    frontier.append(new)
    return spaces


def generic_linear_controls():
    """All block dimensions 1/2 with total dimension <=4, up to block order."""
    cases = subsets_checked = nonsubdirect = 0
    for dimensions in [(1,), (2,), (1, 1), (1, 2), (2, 2), (1, 1, 1), (1, 1, 2), (1, 1, 1, 1)]:
        masks = block_masks(dimensions)
        n = sum(dimensions)
        for rowspace in all_rowspaces(n):
            local_rows = [r for r in rowspace if sum(bool(r & mask) for mask in masks) <= 2]
            if span(local_rows) != rowspace:
                continue
            _, checked = linear_projection_controls(dimensions, local_rows)
            cases += 1
            subsets_checked += checked
            for i, j in combinations(range(len(dimensions)), 2):
                mask = masks[i] | masks[j]
                local = {value for value in range(1 << n) if value & ~mask == 0
                         and all(not dot(row, value) for row in local_rows if row & ~mask == 0)}
                if {v & masks[i] for v in local} != {v for v in range(1 << n) if v & ~masks[i] == 0}:
                    nonsubdirect += 1
    require(nonsubdirect > 0, 'generic local groups explicitly include nonsubdirect cases')
    return cases, subsets_checked, nonsubdirect


def run_controls():
    hidden_candidates, hidden_blocked, hidden_subsets = hidden_parity_model()
    moving_candidates, moving_blocked, moving_partials = moving_owner_model()
    entire_subsets, entire_partials = entire_named_sort_model()
    linear_cases, linear_subsets, nonsubdirect = generic_linear_controls()
    print(f'Finite-kernel controls passed: named 10-point hidden-parity model has 4 actual automorphisms, '
          f'{hidden_candidates} finite motion candidates/{hidden_blocked} blocked, {hidden_subsets} linear projections; '
          f'unnamed-owner S3 model has 6 actual automorphisms, trivial owner kernel, '
          f'{moving_candidates} motion candidates/{moving_blocked} blocked, {moving_partials} partial isometries; '
          f'entire named-sort homogeneous model: {entire_subsets} projections/{entire_partials} partial isometries; '
          f'{linear_cases} exhaustive small binary-generated rowspaces/{linear_subsets} projections '
          f'({nonsubdirect} nonsubdirect local examples). '
          'All finite subsets include empty. No countable compactness, CCO, or exact-owner claim is certified.')


def main():
    run_controls()


if __name__ == '__main__':
    main()
