#!/usr/bin/env python3
"""Finite combinatorial/owner controls for the foundational and safe geometry.

Enumerate actual partitions and all subset cliques; independently enumerate
all colour automorphisms of fully named F2 difference structures (<=8 points).
The Cartesian-phase example is a literal 3 x 3 x F2 pair-table toy.

Finite intersection/preimage tests concern ONLY cardinalities and kernels.
Model-theoretic acl on a finite structure is trivial and is NOT tested here.
These controls certify neither an infinite exact source nor homogeneity,
AP, CCO, harmlessness, safety, acl projection/reconstruction, or EPPA.  They
do not test an infinite-index/coset-avoidance theorem using finite groups.
No other control script or precomputed mathematical answer is imported.
"""

from collections import Counter
from itertools import combinations, permutations, product
from time import perf_counter


def require(condition, message):
    if not condition:
        raise AssertionError(message)


def subsets(values):
    values = tuple(values)
    for size in range(len(values) + 1):
        for chosen in combinations(values, size):
            yield frozenset(chosen)


def partitions(n):
    def visit(labels):
        if len(labels) == n:
            yield tuple(frozenset(i for i, label in enumerate(labels) if label == j)
                        for j in range(max(labels, default=-1) + 1))
            return
        for label in range(max(labels, default=-1) + 2):
            yield from visit(labels + (label,))

    yield from visit(())


def relation(blocks):
    return frozenset((x, y) for block in blocks for x in block for y in block)


def check_rooks(counts):
    sizes = []
    for n in range(5):
        points = frozenset(range(n))
        models = tuple(partitions(n))
        relations = tuple(relation(p) for p in models)
        require(len(relations) == len(set(relations)), 'partition enumeration is unique')
        sizes.append(len(models))
        for clique in subsets(points):
            pairs = frozenset(combinations(sorted(clique), 2))
            concentrated = tuple(any(clique <= b for b in p) or not clique for p in models)
            premises = {(i, j): pairs <= (relations[i] | relations[j])
                        for i in range(len(models)) for j in range(len(models))}
            for (i, j), premise in premises.items():
                counts['two_equivalence_rook_inputs'] += 1
                if premise:
                    require(concentrated[i] or concentrated[j],
                            'two-equivalence rook lemma on every subset clique')
                    counts['two_equivalence_rook_premises'] += 1
            # Indexed families include repeats and the empty family.
            for size in range(4):
                for family in product(range(len(models)), repeat=size):
                    counts['partition_family_clique_inputs'] += 1
                    if all(premises[i, j] for i, j in combinations(family, 2)):
                        require(sum(not concentrated[i] for i in family) <= 1,
                                'pairwise rook premises imply at most one unconcentrated index')
                        counts['one_free_family_premises'] += 1
    require(sizes == [1, 1, 2, 5, 15], 'all 24 partitions on labelled carriers n=0..4')

    triangle = frozenset(range(3))
    weak = (((0, 1), (2,)), ((0, 2), (1,)), ((1, 2), (0,)))
    relations = tuple(relation(p) for p in weak)
    require(all(any((x, y) in r for r in relations) for x, y in combinations(triangle, 2)),
            'negative: three-equivalence union covers the clique')
    require(all(not any(triangle <= frozenset(b) for b in p) for p in weak),
            'negative: all THREE indices are unconcentrated')
    require(not all(all((x, y) in relations[i] | relations[j]
                        for x, y in combinations(triangle, 2))
                    for i, j in combinations(range(3), 2)),
            'negative: union-of-three does not supply pairwise rook premises')
    counts['negative_union_of_three_equivalences'] += 1
    return sizes


def subspaces(points):
    return tuple(k for k in subsets(points) if 0 in k
                 and all(x ^ y in k for x in k for y in k))


def cosets(points, kernel):
    return frozenset(frozenset(x ^ k for k in kernel) for x in points)


def check_difference_model(n, counts):
    points = tuple(range(1 << n))
    # ALL permutations are tried, rather than supplying a translation subgroup.
    automorphisms = tuple(a for a in permutations(points)
                          if all((a[x] ^ a[y]) == (x ^ y) for x in points for y in points))
    require(len(automorphisms) == len(points), 'fully named difference automorphisms enumerated')
    require(all(any(a[x] == y for a in automorphisms) for x in points for y in points),
            'enumerated colour group is transitive')
    kernels = subspaces(points)
    require(len(kernels) == [1, 2, 5, 16][n], 'all subspaces from literal subset closure')
    quotient = {k: cosets(points, k) for k in kernels}
    projection = {k: {x: next(c for c in quotient[k] if x in c) for x in points}
                  for k in kernels}
    counts['difference_models'] += 1
    counts['enumerated_automorphisms'] += len(automorphisms)
    counts['subspace_kernels'] += len(kernels)

    for k in kernels:
        # The actual orbit of (x,d), computed using EVERY enumerated action,
        # is determined exactly by the quotient difference [x xor rep(d)]_K.
        mixed_orbits = {}
        for x, d in product(points, quotient[k]):
            orbital = frozenset((a[x], frozenset(a[y] for y in d)) for a in automorphisms)
            colour = projection[k][x ^ min(d)]
            require(colour not in mixed_orbits or mixed_orbits[colour] == orbital,
                    'mixed real/owner orbital depends only on quotient pair colour')
            mixed_orbits[colour] = orbital
            counts['actual_mixed_pair_inputs'] += 1
        require(len(set(mixed_orbits.values())) == len(mixed_orbits),
                'different mixed readouts are different actual orbitals')

    for k, l in product(kernels, repeat=2):
        joined = frozenset(x ^ y for x in k for y in l)
        seen = {}
        for d, e in product(quotient[k], quotient[l]):
            orbital = frozenset((frozenset(a[x] for x in d), frozenset(a[y] for y in e))
                                for a in automorphisms)
            colour = projection[joined][min(d) ^ min(e)]
            require(colour not in seen or seen[colour] == orbital,
                    'actual two-owner mixed orbital has the common-quotient readout')
            seen[colour] = orbital
            counts['actual_owner_pair_inputs'] += 1
        require(len(set(seen.values())) == len(seen), 'owner mixed readout is exact')

    for size in range(1, 4):
        for family in product(kernels, repeat=size):
            kernel = frozenset.intersection(*family)
            image = {x: tuple(projection[k][x] for k in family) for x in points}
            fibres = {t: frozenset(x for x in points if image[x] == t)
                      for t in set(image.values())}
            require(frozenset(fibres.values()) == cosets(points, kernel),
                    'joint quotient map fibres are exactly common-kernel classes')
            # Same-sort quotient differences reconstruct the full named
            # original fine colour precisely when the common kernel is zero.
            readout = {d: tuple(projection[k][d] for k in family) for d in points}
            require((len(set(readout.values())) == len(points)) == (kernel == {0}),
                    'joint quotient fine-colour readout has exactly the common kernel')
            if kernel == {0}:
                counts['identity_kernel_fine_readouts'] += 1
            counts['joint_kernel_families'] += 1

    # All chosen-owner subsets are tested for each of these named families.
    # These are cardinality tests, never an assertion about model-theoretic acl.
    examples = [(frozenset((0,)),)]
    if n == 2:
        examples += [(frozenset((0, 1)), frozenset((0, 2))),
                     (frozenset((0, 1)), frozenset((0, 2)), frozenset((0, 3)))]
    if n == 3:
        examples += [(frozenset((0, 1, 2, 3)), frozenset((0, 2, 4, 6))),
                     (frozenset((0, 2, 4, 6)), frozenset((0, 1, 4, 5)),
                      frozenset((0, 1, 2, 3)))]
    for family in examples:
        kernel = frozenset.intersection(*family)
        image = {x: tuple(projection[k][x] for k in family) for x in points}
        for selected in product(*(tuple(subsets(quotient[k])) for k in family)):
            w = frozenset(x for x in points
                          if all(projection[k][x] in d for k, d in zip(family, selected)))
            tuples = frozenset(image[x] for x in w)
            bound = len(kernel)
            for d in selected:
                bound *= len(d)
            require(len(w) == len(kernel) * len(tuples) <= bound,
                    'full preimage intersection is a finite union of finite kernel fibres')
            require(all(frozenset(y for y in points if image[y] == image[x]) <= w for x in w),
                    'whole W contains complete common-kernel fibres')
            counts['full_preimage_cardinality_inputs'] += 1
            counts['nonempty_preimage_intersections'] += bool(w)


def check_cartesian_phase(counts):
    # M=(row,column,phase), Y=(column,phase), X=(row,phase), T=phase.
    # Colours are (row inequality,column inequality,phase difference).
    # They are orbitals of the explicitly enumerated product action below;
    # this finite action is NOT claimed to be a standing infinite source.
    points = tuple(product(range(3), range(3), range(2)))
    ypoints = tuple(product(range(3), range(2)))
    xpoints = tuple(product(range(3), range(2)))
    colour = lambda a, b: (int(a[0] != b[0]), int(a[1] != b[1]), a[2] ^ b[2])
    xcolour = lambda a, b: (int(a[0] != b[0]), a[1] ^ b[1])
    ycolour = xcolour
    actions = tuple({(r, c, p): (rp[r], cp[c], p ^ flip) for r, c, p in points}
                    for rp, cp, flip in product(permutations(range(3)),
                                                permutations(range(3)), range(2)))
    atoms = {a: frozenset((u, v) for u, v in product(points, repeat=2) if colour(u, v) == a)
             for a in product(range(2), repeat=3)}
    for a, pairs in atoms.items():
        u, v = next(iter(pairs))
        require(frozenset((g[u], g[v]) for g in actions) == pairs,
                'Cartesian-phase colour atom is the full specified-action orbital')
        counts['cartesian_phase_atom_orbits'] += 1
    require(len(actions) == 72, 'all row/column permutations and phase flips enumerated')

    rectangle = frozenset((y, x) for y, x in product(ypoints, xpoints) if y[1] == x[1])
    actual = frozenset(((c, p), (r, p)) for r, c, p in points)
    require(rectangle == actual and len(rectangle) == len(points) == 18,
            'literal full compatible rectangle is exactly the actual toy carrier')
    for t, tt in product(range(2), repeat=2):
        table = frozenset(xcolour(p, pp) for p, pp in product(xpoints, repeat=2)
                          if p[1] == t and pp[1] == tt)
        require(table == {(0, t ^ tt), (1, t ^ tt)},
                'complete X pair table over every ordered owner pair, including equality')
        counts['complementary_ordered_owner_tables'] += 1

    # Palette S is row-different OR column-different; add logical equality
    # separately when treating it as a reflexive relation.  In particular
    # the phase twin atom (0,0,1) stays unsafe.
    identity = (0, 0, 0)
    safe = frozenset(a for a in atoms if a[0] or a[1])
    reflexive_safe = safe | {identity}
    full_safe, existential_safe = set(), set()
    for y, yy in product(ypoints, repeat=2):
        q = ycolour(y, yy)
        lifts = frozenset(colour(u, v) for u, v in product(points, repeat=2)
                          if (u[1], u[2]) == y and (v[1], v[2]) == yy)
        helper = frozenset(colour((p[0], y[0], y[1]), (pp[0], yy[0], yy[1]))
                           for p, pp in product(xpoints, repeat=2)
                           if p[1] == y[1] and pp[1] == yy[1])
        require(helper == lifts, 'complete complementary helper realizes EVERY fine lift')
        if lifts <= reflexive_safe:
            full_safe.add(q)
        if lifts & reflexive_safe:
            existential_safe.add(q)
        if y != yy:
            require(identity not in lifts, 'distinct projected pairs have no original equality lift')
            counts['all_ordered_distinct_y_pairs'] += 1
            counts['full_helper_fine_lifts'] += len(lifts)
            # Deliberately omit diagonal ENTRIES from the helper pair table.
            # This is not an actual nonempty full rectangle: such a rectangle
            # automatically has diagonal entries.
            incomplete = frozenset(colour((p[0], y[0], y[1]), (pp[0], yy[0], yy[1]))
                                   for p, pp in product(xpoints, repeat=2)
                                   if p != pp and p[1] == y[1] and pp[1] == yy[1])
            if q == (1, 0):
                require(lifts - incomplete == {(0, 1, 0)},
                        'negative: omitting X diagonal loses exactly fine atom (0,1,0)')
                counts['negative_missing_x_diagonal_pairs'] += 1
    require((0, 0) in full_safe <= existential_safe,
            'both projected reflexive relations preserve logical diagonal')
    require(existential_safe - full_safe == {(0, 1)},
            'negative: existential projected safety accepts an unsafe phase twin lift')
    require((0, 0, 1) not in safe and (1, 0, 1) in safe,
            'the same distinct Y colour has unsafe and safe original lifts')
    counts['negative_existential_vs_full_support_palette'] += 1


def main():
    start = perf_counter()
    counts = Counter()
    partition_counts = check_rooks(counts)
    for n in range(4):
        check_difference_model(n, counts)
    check_cartesian_phase(counts)
    require(counts['negative_missing_x_diagonal_pairs'] == 12
            and counts['all_ordered_distinct_y_pairs'] == 30,
            'complete Cartesian-phase distinct-pair coverage')
    print('ACL/owner finite controls passed (Python standard library).')
    print(f'  partitions_by_carrier_n_0_to_4: {partition_counts}; total={sum(partition_counts)}')
    for key, value in sorted(counts.items()):
        print(f'  {key}: {value}')
    print(f'  elapsed_seconds: {perf_counter() - start:.3f}')
    print('Scope: all subset cliques, indexed partition families of sizes 0..3, '
          'all colour automorphisms on fully named F2 carriers 1,2,4,8, '
          'all subspace families of sizes 1..3; selected preimage cardinality families; '
          '3x3xF2 pair table with all 30 ordered distinct Y pairs.')
    print('Preimage controls establish finite cardinalities ONLY, not model-theoretic acl. '
          'No infinite-source, homogeneity, AP, CCO, harmlessness, safety, '
          'acl projection/reconstruction, infinite-index avoidance, or EPPA certification.')


if __name__ == '__main__':
    main()
