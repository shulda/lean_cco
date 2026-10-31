#!/usr/bin/env python3
"""Independent bounded RAW trace/quotient/full-phase diagnostics for B062.

The finite hierarchical orbital model has 16 actual points, a two-point
clone gate, and three genuine hierarchical phase directions. It is not
claimed to certify unbounded AP/CCO, terminality or the source theorems.
"""
from itertools import combinations, product
import json
import time


POINTS = tuple(range(16))
ATOMS = tuple(frozenset(a) for a in ((0,), (1,), (2, 3), range(4, 8), range(8, 16)))
TOP = frozenset(POINTS)
ID = frozenset((0,))
GATES = tuple(frozenset(range(n)) for n in (2, 4, 8))
ORBIT_KERNELS = tuple(frozenset(range(n)) for n in (4, 8, 16))


def mul(a, b):
    return frozenset(x ^ y for x in a for y in b)


def compose(a, b):
    right = {}
    for y, z in b:
        right.setdefault(y, set()).add(z)
    return frozenset((x, z) for x, y in a for z in right.get(y, ()))


def closure(atoms, top, identity, operation):
    reachable = set(atoms) | {identity}
    while True:
        additions = {operation(a, b) for a in reachable for b in reachable}
        additions.discard(frozenset())
        if additions <= reachable:
            break
        reachable.update(additions)
    exact = reachable | {top}
    while True:
        additions = {a & b for a in exact for b in exact if a & b}
        if additions <= exact:
            break
        exact.update(additions)
    return tuple(sorted(exact, key=lambda a: (len(a), sorted(a))))


EXACT = closure(ATOMS, TOP, ID, mul)
EQUIVALENCES = tuple(d for d in EXACT if 0 in d and mul(d, d) == d)
OLD_RELATIONS = {d: frozenset((x, y) for x in POINTS for y in POINTS if x ^ y in d)
                 for d in EXACT}


def classes(kernel):
    return tuple(sorted({frozenset(x ^ k for k in kernel) for x in POINTS}, key=min))


def partition(labels):
    return {label: frozenset(x for x in POINTS if labels[x] == label)
            for label in sorted(set(labels))}


def type_support(domain, labels):
    return frozenset((labels[x], labels[y]) for x in POINTS for y in POINTS if x ^ y in domain)


def make_tower(seed1, seed2, delta, gauge):
    one = tuple(((x >> 1) & 1) ^ ((seed1 >> (x >> 2)) & 1) for x in POINTS)
    two = tuple(((x >> 2) & 1) ^ ((seed2 >> (x >> 3)) & 1) ^ (delta & one[x])
                for x in POINTS)
    three = tuple(((x >> 3) & 1) ^ ((gauge >> ((one[x] << 1) | two[x])) & 1)
                  for x in POINTS)
    bits = (one, two, three)
    prefixes = [tuple(() for _ in POINTS)]
    for j in range(1, 4):
        prefixes.append(tuple(tuple(bits[i][x] for i in range(j)) for x in POINTS))
    # h is the fixed character potential; seeds on its orbit blocks are free.
    potentials = (tuple((x >> 1) & 1 for x in POINTS),
                  tuple(((x >> 2) & 1) ^ (delta & one[x]) for x in POINTS),
                  three)
    return bits, prefixes, potentials


def check_traces(prefixes, counts):
    for stage, labels in enumerate(prefixes):
        parts = partition(labels)
        traces = {(d, u, v): frozenset((x, y) for x in us for y in vs if x ^ y in d)
                  for d in EXACT for u, us in parts.items() for v, vs in parts.items()}
        for u, v, w in product(parts, repeat=3):
            left = [d for d in EXACT if traces[d, u, v]]
            right = [d for d in EXACT if traces[d, v, w]]
            for d, e in product(left, right):
                assert compose(traces[d, u, v], traces[e, v, w]) == traces[mul(d, e), u, w]
                counts['nonempty_real_trace_products'] += 1
        # Exact restriction fibers and their actual largest old equivalences.
        for p in parts:
            images = {traces[e, p, p] for e in EQUIVALENCES}
            for current in images:
                fiber = [e for e in EQUIVALENCES if traces[e, p, p] == current]
                largest = max(fiber, key=len)
                assert all(e <= largest for e in fiber)
                for old in EQUIVALENCES:
                    assert (traces[old, p, p] <= current) == (old <= largest)
                    counts['largest_lift_adjunctions'] += 1
            if stage < 3:
                gate_trace = traces[GATES[stage], p, p]
                fiber = [e for e in EQUIVALENCES if traces[e, p, p] == gate_trace]
                assert max(fiber, key=len) == GATES[stage]
                counts['canonical_old_gates'] += 1
        # Actual exact class occupancy is the WHOLE Phi-class of every type.
        for e in EQUIVALENCES:
            phi = type_support(e, labels)
            for cell in classes(e):
                occupancy = {labels[x] for x in cell}
                for p in occupancy:
                    assert occupancy == {q for s, q in phi if s == p}
                    counts['complete_class_occupancies'] += 1
        for d, e in product(EXACT, repeat=2):
            if d & e:
                assert type_support(d & e, labels) == type_support(d, labels) & type_support(e, labels)
                counts['nonempty_exact_type_meets'] += 1
        # The prefix common gate is exactly the largest exact label kernel.
        common = TOP if stage == 0 else frozenset.intersection(*GATES[:stage])
        preserving = [e for e in EQUIVALENCES
                      if all(labels[x] == labels[y] for x in POINTS for y in POINTS if x ^ y in e)]
        assert max(preserving, key=len) == common
        identity_types = frozenset((p, p) for p in parts)
        assert type_support(common, labels) == identity_types
        assert (frozenset.intersection(*(type_support(g, labels) for g in GATES[:stage]))
                if stage else frozenset(product(parts, repeat=2))) == identity_types
        counts['common_exact_kernels'] += 1


def check_arbitrary_support_products(labels, counts):
    # Test the stronger Phi composition claim on ALL invariant old unions,
    # independently of the exact-domain-only trace control above.
    domains = tuple(frozenset().union(*(ATOMS[i] for i in range(5) if mask & (1 << i)))
                    for mask in range(32))
    images = {d: type_support(d, labels) for d in domains}
    for d, e in product(domains, repeat=2):
        assert images[mul(d, e)] == compose(images[d], images[e])
        counts['arbitrary_invariant_support_products'] += 1


def check_quotient_atoms_and_exactness(counts):
    for e in EQUIVALENCES:
        cells = classes(e)
        index = {x: i for i, cell in enumerate(cells) for x in cell}
        qtop = frozenset(product(range(len(cells)), repeat=2))
        qid = frozenset((i, i) for i in range(len(cells)))
        images = {a: frozenset((index[x], index[y]) for x in POINTS for y in POINTS if x ^ y in a)
                  for a in ATOMS}
        qatoms = set(images.values())
        assert qid in qatoms
        assert all(a == b or not a & b for a in qatoms for b in qatoms)
        assert frozenset().union(*qatoms) == qtop
        pulled_id = frozenset((x, y) for x in POINTS for y in POINTS if index[x] == index[y])
        assert pulled_id == OLD_RELATIONS[e]
        qexact = closure(qatoms, qtop, qid, compose)
        for d in EXACT:
            if mul(e, mul(d, e)) == d:
                qd = frozenset((index[x], index[y]) for x in POINTS for y in POINTS if x ^ y in d)
                assert qd in qexact
                counts['one_original_sort_exact_descents'] += 1
        if e != ID:
            assert len(qatoms) - 1 < len(ATOMS) - 1
            counts['strict_original_diversity_drops'] += 1
        counts['actual_quotient_atom_partitions'] += len(qatoms)


def all_global_phases(potential, orbit_kernel):
    orbit_cells = classes(orbit_kernel)
    orbit_index = {x: i for i, cell in enumerate(orbit_cells) for x in cell}
    return [tuple(potential[x] ^ ((seed >> orbit_index[x]) & 1) for x in POINTS)
            for seed in range(1 << len(orbit_cells))]


def check_quotient_steps(bits, prefixes, potentials, counts):
    for step in range(3):
        parent, child = prefixes[step], prefixes[step + 1]
        gate, orbit_kernel, potential = GATES[step], ORBIT_KERNELS[step], potentials[step]
        globals_ = all_global_phases(potential, orbit_kernel)
        assert bits[step] in globals_
        for e in EQUIVALENCES:
            cells = classes(e)
            occupancy = [frozenset(parent[x] for x in cell) for cell in cells]
            newoccupancy = [frozenset(child[x] for x in cell) for cell in cells]
            if not e <= gate:
                for i, cell in enumerate(cells):
                    expected = frozenset(p + (b,) for p in occupancy[i] for b in (0, 1))
                    assert newoccupancy[i] == expected
                    for phase in globals_:
                        for p in occupancy[i]:
                            assert {phase[x] for x in cell if parent[x] == p} == {0, 1}
                            counts['every_class_both_child_phase_tests'] += 1
                for i, j in combinations(range(len(cells)), 2):
                    assert (occupancy[i] == occupancy[j]) == (newoccupancy[i] == newoccupancy[j])
                counts['discarded_quotient_steps'] += 1
                continue
            # Independently recover gamma from whole old identity gate transports.
            corrections = {}
            representatives = []
            for i, cell in enumerate(cells):
                occ = occupancy[i]
                base = min(occ)
                gamma = {}
                for p in occ:
                    values = {potential[x] ^ potential[y] for x in POINTS for y in POINTS
                              if parent[x] == base and parent[y] == p and x ^ y in gate}
                    assert len(values) == 1
                    gamma[p] = next(iter(values))
                    counts['nonzero_object_offsets'] += gamma[p]
                assert gamma[base] == 0
                corrections[i] = gamma
                representatives.append(min(x for x in cell if parent[x] == base))
            for occ in set(occupancy):
                gamma = corrections[occupancy.index(occ)]
                actual = {newoccupancy[i] for i in range(len(cells)) if occupancy[i] == occ}
                expected = {frozenset(p + (b ^ gamma[p],) for p in occ) for b in (0, 1)}
                assert actual == expected
                assert all(len({p[:-1] for p in graph}) == len(graph) == len(occ) for graph in actual)
                counts['retained_bijective_occupancy_graphs'] += 2
            images = set()
            for phase in globals_:
                values = []
                for i, cell in enumerate(cells):
                    projected = {phase[x] ^ corrections[i][parent[x]] for x in cell}
                    assert len(projected) == 1
                    values.append(next(iter(projected)))
                images.add(sum(b << i for i, b in enumerate(values)))
            # Enumerate ALL functions on the E-classes and impose the actual
            # full projected character equations, including duplicate gate points.
            constraints = []
            for i, j in combinations(range(len(cells)), 2):
                x, y = representatives[i], representatives[j]
                if x ^ y in orbit_kernel:
                    constraints.append((i, j, potential[x] ^ potential[y]))
                if occupancy[i] == occupancy[j] and x ^ y in gate:
                    assert potential[x] == potential[y]
                    counts['distinct_E_classes_same_gate_point'] += 1
            local = {mask for mask in range(1 << len(cells))
                     if all((((mask >> i) ^ (mask >> j)) & 1) == b for i, j, b in constraints)}
            assert local == images
            counts['full_local_global_phase_bijections'] += 1
            counts['all_quotient_phase_functions_checked'] += 1 << len(cells)
            counts['retained_quotient_steps'] += 1


def main():
    start = time.monotonic()
    assert len(EXACT) == 9 and len(EQUIVALENCES) == 5
    keys = ['nonempty_real_trace_products', 'largest_lift_adjunctions', 'canonical_old_gates',
            'complete_class_occupancies', 'nonempty_exact_type_meets', 'common_exact_kernels',
            'arbitrary_invariant_support_products', 'one_original_sort_exact_descents',
            'strict_original_diversity_drops', 'actual_quotient_atom_partitions',
            'every_class_both_child_phase_tests', 'discarded_quotient_steps',
            'nonzero_object_offsets', 'retained_bijective_occupancy_graphs',
            'distinct_E_classes_same_gate_point', 'full_local_global_phase_bijections',
            'all_quotient_phase_functions_checked', 'retained_quotient_steps']
    counts = dict.fromkeys(keys, 0)
    configurations = list(product((0, 6), (0, 1), (0, 1), (0, 6)))
    for seed1, seed2, delta, gauge in configurations:
        bits, prefixes, potentials = make_tower(seed1, seed2, delta, gauge)
        check_traces(prefixes, counts)
        check_quotient_steps(bits, prefixes, potentials, counts)
    for labels in make_tower(6, 1, 1, 6)[1]:
        check_arbitrary_support_products(labels, counts)
    check_quotient_atoms_and_exactness(counts)
    # Both nonempty input traces are essential, even on a two-point source.
    empty_input = frozenset()
    second = frozenset(((1, 0),))
    assert compose(empty_input, second) == frozenset()
    whole_id = frozenset(((0, 0), (1, 1)))
    whole_top = frozenset(product(range(2), repeat=2))
    right_hand_side = frozenset((x, z) for x, z in compose(whole_id, whole_top) if x == z == 0)
    assert right_hand_side == frozenset(((0, 0),))
    assert compose(empty_input, second) != right_hand_side
    # Phi cannot preserve a disjoint old atomic meet: clone and Id both loop
    # on each final owner type, despite having empty old relation intersection.
    final_labels = make_tower(6, 1, 1, 6)[1][-1]
    assert not (ATOMS[0] & ATOMS[1])
    assert type_support(ATOMS[0], final_labels) & type_support(ATOMS[1], final_labels)
    assert not type_support(frozenset(), final_labels)
    assert counts['nonzero_object_offsets'] and counts['distinct_E_classes_same_gate_point']
    assert time.monotonic() - start < 25
    print(json.dumps(dict(status='PASS_BOUNDED_DIAGNOSTICS_ONLY', points=16,
                          tower_configurations=len(configurations), exact_domains=len(EXACT),
                          exact_equivalences=len(EQUIVALENCES), counts=counts,
                          seconds=round(time.monotonic() - start, 3)), sort_keys=True))


if __name__ == '__main__':
    main()
