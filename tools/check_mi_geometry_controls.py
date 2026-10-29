#!/usr/bin/env python3
"""Independent bounded controls for maximal-core/minimum-ancestor geometry.

Only finite posets, their literal downsets, and actual set partitions are
enumerated.  No claimed CCO source or abstractly supplied lattice answer is
used as input.  In particular, every equivalence on a finite carrier has
finite classes: these tests CANNOT establish absence of nonidentity
finite-class exact equivalences in an infinite normalised source.  They
also do not establish algebraic closure, safety, CCO, or EPPA.

Contracts controlled: the downset calculation in maximal_cores/01 and
the MO/MOR (including JOG) identities in maximal_cores/05; the elementary
class injection and finite uniform-index multiplication used in /01.
The negative examples deliberately drop hypotheses, and are not actual
source or packet-core counterexamples.  Python standard library only.
"""

from collections import Counter
from itertools import combinations, product
from time import perf_counter


def require(condition, message):
    if not condition:
        raise AssertionError(message)


def subsets(values):
    values = tuple(values)
    for size in range(len(values) + 1):
        for chosen in combinations(values, size):
            yield frozenset(chosen)


def intersection(family, top):
    result = frozenset(top)
    for member in family:
        result = result & member
    return result


def labelled_posets(n):
    """All relations, not just orders compatible with one fixed labelling.

    Each unordered pair is absent, forward, or backward.  Add the diagonal
    and keep precisely the transitive relations; antisymmetry is built in.
    This includes orders such as 3 < 0 as well as 0 < 3.
    """
    points = frozenset(range(n))
    pairs = tuple(combinations(range(n), 2))
    for choices in product(range(3), repeat=len(pairs)):
        relation = {(x, x) for x in points}
        for (x, y), choice in zip(pairs, choices):
            if choice == 1:
                relation.add((x, y))
            elif choice == 2:
                relation.add((y, x))
        if all((x, z) in relation
               for x, y in relation for yy, z in relation if y == yy):
            yield points, frozenset(relation)


def downsets(points, order):
    return frozenset(d for d in subsets(points)
                     if all(y not in d or x in d for x, y in order))


def minima(points, order):
    return frozenset(y for y in points
                     if not any(x != y and (x, y) in order for x in points))


def check_poset(points, order, counts):
    lattice = downsets(points, order)
    roots = tuple(sorted(minima(points, order)))
    atoms = frozenset(d for d in lattice if d and
                      not any(e and e < d for e in lattice))
    require(atoms == frozenset(frozenset((p,)) for p in roots),
            'downset atoms are exactly singleton minimal points')
    ancestors = {q: frozenset(p for p in roots if (p, q) in order)
                 for q in points}
    require(all(ancestors.values()), 'every point has a minimal ancestor')
    cores = {p: frozenset(q for q in points if (p, q) not in order)
             for p in roots}
    for p, core in cores.items():
        atom = frozenset((p,))
        require(core in lattice and not core & atom,
                'C_i is a downset disjoint from its atom')
        require(all(q in core for q in roots if q != p),
                'C_i contains every other atom')
        for d in lattice:
            require((not d & atom) == (d <= core),
                    'C_i is the GREATEST atom-disjoint downset')
            counts['greatest_disjoint_tests'] += 1
    require(not intersection(cores.values(), points),
            'meet of the COMPLETE family of atom pseudocomplements is zero')
    counts['complete_core_meets'] += 1

    for selected in subsets(roots):
        if not selected:
            continue
        kernel = intersection((cores[p] for p in selected), points)
        residual = points - kernel
        require(residual == frozenset(q for q in points
                                     if ancestors[q] & selected),
                'complement of K_I is the union of selected principal upsets')
        restricted_order = frozenset((x, y) for x, y in order
                                     if x in residual and y in residual)
        require(minima(residual, restricted_order) == selected,
                'residual minima are EXACTLY the selected original roots')
        interval = frozenset(d for d in lattice if kernel <= d)
        residual_lattice = downsets(residual, restricted_order)
        require(frozenset(d - kernel for d in interval) == residual_lattice,
                'upper interval maps onto all residual downsets')
        require(frozenset(kernel | d for d in residual_lattice) == interval,
                'residual downsets lift back to the entire upper interval')
        for d in interval:
            require(kernel | (d - kernel) == d, 'interval map is injective')
        quotient_atoms = frozenset(d for d in interval if d != kernel and
                                  not any(kernel < e < d for e in interval))
        require(quotient_atoms == frozenset(kernel | {p} for p in selected),
                'minimal nonzero interval elements are E_i join K_I')
        counts['selected_root_intervals'] += 1
        counts['interval_elements'] += len(interval)

    counts['downsets'] += len(lattice)
    if any(x != y for x, y in order):
        counts['nonboolean_downset_lattices'] += 1
    if len(roots) < 2:
        return
    counts['multiple_root_posets'] += 1
    if any(len(a) > 1 for a in ancestors.values()):
        counts['shared_ancestor_posets'] += 1
    joins = {(p, q): cores[p] | cores[q] for p, q in combinations(roots, 2)}
    owners = {p: intersection((cores[p] | cores[q] for q in roots if q != p),
                              points) for p in roots}
    star = intersection(joins.values(), points)
    for (p, q), join in joins.items():
        require(join == frozenset(x for x in points
                                 if not {p, q} <= ancestors[x]), 'MO: J_ij formula')
        require(owners[p] | owners[q] == join, 'JOG: H_i join H_j = J_ij')
        counts['ancestor_pair_and_jog_tests'] += 1
    for p, owner in owners.items():
        require(owner == frozenset(x for x in points
                                  if p not in ancestors[x] or ancestors[x] == {p}),
                'MO: H_i formula')
        require(cores[p] <= owner, 'C_i <= H_i')
        counts['ancestor_owner_tests'] += 1
    require(star == frozenset(x for x in points if len(ancestors[x]) == 1),
            'MO: H_star consists exactly of points with one minimal ancestor')
    require(star and frozenset(roots) <= star,
            'MOR: H_star > zero (it may equal top)')
    require(intersection(owners.values(), points) == star, 'MOR: meet H_i = H_star')
    require(star in lattice and all(h in lattice for h in owners.values()),
            'all owner cuts remain downsets')
    counts['strict_positive_owner_cuts'] += 1


def partitions(n):
    """Actual partitions via unique restricted-growth strings."""
    def visit(labels):
        if len(labels) == n:
            yield tuple(frozenset(i for i, label in enumerate(labels) if label == j)
                        for j in range(max(labels, default=-1) + 1))
            return
        for label in range(max(labels, default=-1) + 2):
            yield from visit(labels + (label,))

    yield from visit(())


def equivalence(blocks):
    return frozenset((x, y) for block in blocks for x in block for y in block)


def classes(relation, points):
    return frozenset(frozenset(y for y in points if (x, y) in relation)
                     for x in points)


def uniform_index(lower, upper):
    """[upper:lower], only when nonempty and constant on upper classes."""
    values = {sum(c <= h for c in lower) for h in upper}
    return next(iter(values)) if len(values) == 1 else None


def check_partitions(n, counts):
    points = frozenset(range(n))
    models = tuple((frozenset(p), equivalence(p)) for p in partitions(n))
    require(len(models) == len({r for _, r in models}), 'partitions enumerated uniquely')
    diagonal = frozenset((x, x) for x in points)
    for (eb, e), (kb, k), (hb, h) in product(models, repeat=3):
        counts['partition_triples'] += 1
        if k <= h and e & k == diagonal:
            # The map on each E meet H class is literally x |-> [x]_K.
            # Its codomain is the K-classes within that class's H-class.
            for block in classes(e & h, points):
                ambient = next(b for b in hb if block <= b)
                codomain = frozenset(b for b in kb if b <= ambient)
                images = tuple(next(b for b in kb if x in b) for x in sorted(block))
                require(set(images) <= codomain and len(set(images)) == len(block),
                        'each E meet H class injects into its H/K class set')
                require(len(block) <= len(codomain), 'finite class-size injection bound')
                counts['injected_classes'] += 1
            counts['class_injection_triples'] += 1
        if e <= k <= h:
            # Here e is the lower member C of the chain C <= K <= H.
            for ambient in hb:
                require(sum(c <= ambient for c in eb)
                        == sum(sum(c <= b for c in eb) for b in kb if b <= ambient),
                        'nonuniform local index is the sum over intermediate classes')
                counts['local_nested_index_sums'] += 1
            hk, kc, hc = (uniform_index(kb, hb), uniform_index(eb, kb),
                          uniform_index(eb, hb))
            if hk is not None and kc is not None:
                require(hc == hk * kc, 'uniform nested indices multiply')
                counts['uniform_nested_index_triples'] += 1
                if hk > 1 and kc > 1:
                    counts['nontrivial_index_products'] += 1
    return len(models)


def negative_controls(counts):
    # Keep all other atoms and zero common meet, but lose maximality.
    # P has roots 0,1 and 0<2.  The second true core is {0,2}.
    points = frozenset(range(3))
    order = frozenset(((0, 0), (1, 1), (2, 2), (0, 2)))
    lattice = downsets(points, order)
    weak = (frozenset((1,)), frozenset((0,)))
    require(all(c in lattice and i not in c and (1 - i) in c
                for i, c in enumerate(weak)) and not weak[0] & weak[1],
            'negative: weakened cores retain disjointness, other atoms, zero meet')
    residual = points - weak[1]
    require(minima(residual, order) == {1, 2},
            'negative: nonmaximal core creates an extra residual minimum')
    require(weak[0] | weak[1] != points,
            'negative: weak J_01 and H_star violate the original-ancestor formulas')
    counts['negative_nonmaximal_core_witnesses'] += 1

    # In M3 an atom has two incomparable maximal disjoint elements and
    # NO greatest disjoint element.  Thus the pseudocomplement premise fails.
    elements = frozenset(('0', 'a', 'b', 'c', '1'))

    def le(x, y):
        return x == y or x == '0' or y == '1'

    def bound(x, y, upper):
        candidates = {z for z in elements
                      if (le(x, z) and le(y, z) if upper else le(z, x) and le(z, y))}
        best = [z for z in candidates if all(le(z, w) if upper else le(w, z)
                                            for w in candidates)]
        require(len(best) == 1, 'negative: M3 has unique binary lattice bounds')
        return best[0]

    meet = lambda x, y: bound(x, y, False)
    join = lambda x, y: bound(x, y, True)
    disjoint = {x for x in elements if meet('a', x) == '0'}
    require(not any(all(le(y, x) for y in disjoint) for x in disjoint),
            'negative: M3 has no atom pseudocomplement')
    require(meet('a', join('b', 'c')) != join(meet('a', 'b'), meet('a', 'c')),
            'negative: M3 fails distributivity')
    counts['negative_m3_witnesses'] += 1

    # A proper sublist of atoms need not give zero common pseudocomplement.
    full_cores = (frozenset((1,)), frozenset((0,)))
    require(intersection(full_cores[:1], {0, 1}) == {1}
            and not intersection(full_cores, {0, 1}),
            'negative: complete atom list is necessary for meet-all = zero')
    counts['negative_incomplete_atom_list_witnesses'] += 1

    # The ancestor statement with r>=2 also needs EXHAUSTIVE minima.
    # Selecting two roots in a three-point antichain leaves one Anc empty.
    omitted_points = frozenset((0, 1, 2))
    partial_roots = frozenset((0, 1))
    partial_ancestors = {q: frozenset((q,)) & partial_roots for q in omitted_points}
    actual_star = (omitted_points - {0}) | (omitted_points - {1})
    formula_star = frozenset(q for q, ancestors in partial_ancestors.items()
                            if len(ancestors) == 1)
    require(not partial_ancestors[2] and actual_star != formula_star,
            'negative: incomplete r>=2 minima falsify the H_star ancestor formula')
    counts['negative_incomplete_ancestor_formula_witnesses'] += 1

    # Finite carriers have finite-class nonidentity equivalences.  This is
    # precisely why the finite partition tests cannot certify normalisation.
    diagonal = equivalence((frozenset((0,)), frozenset((1,))))
    top = equivalence((frozenset((0, 1)),))
    require(diagonal < top and len(classes(top, {0, 1})) == 1,
            'boundary: a finite carrier has a nonidentity finite-class relation')
    counts['finite_class_boundary_witnesses'] += 1


def main():
    start = perf_counter()
    counts = Counter()
    poset_counts = []
    for n in range(5):
        orders = tuple(labelled_posets(n))
        require(len(orders) == len({order for _, order in orders}), 'orders are unique')
        poset_counts.append(len(orders))
        for points, order in orders:
            check_poset(points, order, counts)
    require(poset_counts == [1, 1, 3, 19, 219], 'all 243 labelled posets for n=0..4')
    partition_counts = [check_partitions(n, counts) for n in range(5)]
    require(partition_counts == [1, 1, 2, 5, 15], 'all 24 partitions for n=0..4')
    require(counts['shared_ancestor_posets'] and counts['nonboolean_downset_lattices']
            and counts['nontrivial_index_products'], 'nonvacuous structural coverage')
    negative_controls(counts)
    print('MI geometry controls passed (stdlib; labelled posets and finite carriers n=0..4).')
    print(f'  labelled_posets_by_n: {poset_counts}; total={sum(poset_counts)}')
    print(f'  partitions_by_n: {partition_counts}; total={sum(partition_counts)}')
    for key, value in sorted(counts.items()):
        print(f'  {key}: {value}')
    print(f'  elapsed_seconds: {perf_counter() - start:.3f}')
    print('Bounds: all downsets, all nonempty root selections, all partition triples in these sizes. '
          'H_star > zero does not require H_star < top. Negative controls drop stated hypotheses.')
    print('Finite-class/infinite-source boundary: NO absence-of-finite-exact-quotients, acl, '
          'safety, CCO, EPPA, or general theorem/Lean certification.')


if __name__ == '__main__':
    main()
