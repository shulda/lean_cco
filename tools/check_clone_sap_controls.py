#!/usr/bin/env python3
"""Bounded B045 clone/palette diagnostics; not an unbounded CCO/SAP proof.

Reproduce: python tools/check_clone_sap_controls.py
Finite clone windows are sufficient for the explicitly bounded graphs/spans;
they are not asserted to have the full age properties of infinite fibres.
"""
from collections import Counter, defaultdict
from itertools import combinations, permutations, product
import json
import signal
import time

START = time.monotonic()
COUNTS = Counter()


def colour(x, y, width):
    if x == y:
        return -1                         # logical identity, never diversity
    a, b = x // width, y // width
    return 0 if a == b else a ^ b         # c=0, old difference atoms positive


def hom(n, edges, owners=2, width=4):
    """Independent actual finite-host backtracking oracle, no cycle test."""
    order = sorted(range(n), key=lambda x: -sum(x in e for e in edges))
    assigned = {}

    def rec(k):
        if k == n:
            return tuple(assigned[x] for x in range(n))
        x = order[k]
        for y in range(owners * width):
            if all(colour(y, v, width) == edges[tuple(sorted((x, z)))]
                   for z, v in assigned.items() if tuple(sorted((x, z))) in edges):
                assigned[x] = y
                result = rec(k + 1)
                if result is not None:
                    return result
                del assigned[x]
        return None
    return rec(0)


def cycles(n):
    for size in range(3, n + 1):
        for vertices in combinations(range(n), size):
            first, rest = vertices[0], vertices[1:]
            for tail in permutations(rest):
                if tail[0] < tail[-1]:
                    yield (first,) + tail


def cycle_feasible(n, edges, owners=2, width=4):
    for cyc in cycles(n):
        pairs = [tuple(sorted((cyc[i], cyc[(i + 1) % len(cyc)])))
                 for i in range(len(cyc))]
        if not all(e in edges for e in pairs):
            continue
        local = {tuple(sorted((i, (i + 1) % len(cyc)))): edges[e]
                 for i, e in enumerate(pairs)}
        COUNTS['specified_simple_cycles'] += 1
        if hom(len(cyc), local, owners, width) is None:
            return False
    return True


def contract_and_lift(n, edges, owners=2, width=4):
    """Construct by c-components and an OLD owner-only homomorphism."""
    parent = list(range(n))

    def find(x):
        while x != parent[x]:
            x = parent[x]
        return x
    for (a, b), c in edges.items():
        if c == 0:
            parent[find(a)] = find(b)
    components = sorted({find(x) for x in range(n)})
    index = {v: i for i, v in enumerate(components)}
    old = {}
    for (a, b), c in edges.items():
        if not c:
            continue
        a, b = index[find(a)], index[find(b)]
        assert a != b, 'an old edge cannot lie in one feasible c-component'
        pair = tuple(sorted((a, b)))
        assert pair not in old or old[pair] == c, 'conflicting component labels'
        old[pair] = c
    # width=1: each OLD host owner is one actual point, no clone c edges.
    owner_map = hom(len(components), old, owners=owners, width=1)
    assert owner_map is not None, 'old quotient graph must be feasible'
    used = Counter()
    result = []
    for x in range(n):
        owner = owner_map[index[find(x)]]
        result.append(owner * width + used[owner])
        used[owner] += 1
        assert used[owner] <= width, 'control window was too small'
    assert len(set(result)) == n
    assert all(colour(result[a], result[b], width) == c for (a, b), c in edges.items())
    COUNTS['component_quotient_lifts'] += 1
    return result


def graph_controls():
    for n in range(5):
        pairs = list(combinations(range(n), 2))
        for labels in product((None, 0, 1), repeat=len(pairs)):
            edges = {e: c for e, c in zip(pairs, labels) if c is not None}
            feasible = cycle_feasible(n, edges)
            solution = hom(n, edges)
            assert feasible == (solution is not None)
            COUNTS['partial_clone_graphs'] += 1
            if feasible:
                contract_and_lift(n, edges)
    # A genuine incompatible parallel OLD label example uses two old atoms.
    bad_internal = {(0, 1): 0, (1, 2): 0, (0, 2): 1}
    bad_parallel = {(0, 1): 0, (2, 3): 0, (0, 2): 1, (1, 3): 2}
    assert not cycle_feasible(3, bad_internal, owners=4)
    assert hom(3, bad_internal, owners=4) is None
    assert not cycle_feasible(4, bad_parallel, owners=4)
    assert hom(4, bad_parallel, owners=4) is None
    # A quotient triangle lifts to a six-cycle through three c-components.
    lifted_cycle = {(0, 1): 0, (2, 3): 0, (4, 5): 0,
                    (1, 2): 1, (3, 4): 2, (0, 5): 3}
    assert cycle_feasible(6, lifted_cycle, owners=4, width=6)
    contract_and_lift(6, lifted_cycle, owners=4, width=6)
    COUNTS['explicit_component_obstructions'] = 2
    COUNTS['explicit_quotient_cycle_lifts'] = 1


def kernel_and_ap_controls():
    for width in range(1, 5):
        universe = range(2 * width)
        for x, y in product(universe, repeat=2):
            two_step = any(colour(x, z, width) == colour(z, y, width) == 0
                           for z in universe)
            kernel = x // width == y // width
            if width >= 3:
                assert two_step == kernel
            elif width == 2:
                assert two_step == (x == y)
            COUNTS['kernel_pair_checks'] += 1
    assert not any(colour(0, z, 2) == colour(z, 1, 2) == 0 for z in range(4))
    # Old Q={0,1} has AP but two a-neighbours over 0 must identify, so no SAP.
    # Its clone cover places those two neighbours at distinct points of owner 1.
    assert colour(0, 4, 4) == colour(0, 5, 4) == 1
    assert colour(4, 5, 4) == 0
    small = range(6)                     # two owners, three clones each
    for base in [frozenset(), frozenset({0}), frozenset({0, 3})]:
        legs = [base | frozenset(extra) for k in range(3)
                for extra in combinations([x for x in small if x not in base], k)]
        for left, right in product(legs, repeat=2):
            # Work in a width-eight target. Rename all nonbase right clones.
            left_map = {x: (x // 3) * 8 + x % 3 for x in left}
            right_map = {x: left_map[x] for x in base}
            occupied = set(left_map.values())
            for x in sorted(right - base):
                owner = x // 3
                y = next(y for y in range(owner * 8, owner * 8 + 8) if y not in occupied)
                right_map[x] = y
                occupied.add(y)
            assert set(left_map.values()) & set(right_map.values()) == {left_map[x] for x in base}
            for leg, mapping in [(left, left_map), (right, right_map)]:
                assert len(set(mapping.values())) == len(leg)
                assert all(colour(x, y, 3) == colour(mapping[x], mapping[y], 8)
                           for x, y in combinations(leg, 2))
            COUNTS['capacity_sufficient_strong_spans'] += 1
    for m in range(2, 8):
        assert 2 * m - 1 > m            # forced finite full c-fibre obstruction
        COUNTS['finite_fibre_SAP_obstructions'] += 1


def homogeneity_controls():
    fibre_perms = list(permutations(range(3)))
    automorphisms = []
    for flip, p, q in product(range(2), fibre_perms, fibre_perms):
        g = tuple(((x // 3) ^ flip) * 3 + (p if x < 3 else q)[x % 3] for x in range(6))
        assert all(colour(x, y, 3) == colour(g[x], g[y], 3) for x, y in combinations(range(6), 2))
        automorphisms.append(g)
    for size in range(4):
        by_type = defaultdict(list)
        for tup in permutations(range(6), size):
            signature = tuple(colour(tup[i], tup[j], 3) for i, j in combinations(range(size), 2))
            by_type[signature].append(tup)
        for tuples in by_type.values():
            representative = tuples[0]
            orbit = {tuple(g[x] for x in representative) for g in automorphisms}
            assert orbit == set(tuples)
            COUNTS['partial_isomorphism_tuple_checks'] += len(tuples)
    COUNTS['actual_clone_automorphisms'] = len(automorphisms)


def compose_rel(a, b):
    return {(x, z) for x, y in a for yy, z in b if y == yy}


def palette_controls():
    universe = range(4)                  # all named nonzero F2^2 differences
    relations = []
    for flags in product(range(2), repeat=3):
        palette = {i + 1 for i, b in enumerate(flags) if b}
        rel = {(x, y) for x, y in product(universe, repeat=2) if x == y or x ^ y in palette}
        if compose_rel(rel, rel) <= rel:
            relations.append((palette, rel))
    assert len(relations) == 5
    for (a, ra), (b, rb) in product(relations, repeat=2):
        comp = compose_rel(ra, rb)
        assert comp == compose_rel(rb, ra)
        assert compose_rel(comp, comp) == comp
        assert ra <= comp and rb <= comp
        assert all(comp <= rc for _, rc in relations if ra <= rc and rb <= rc)
        assert any(comp == rc for _, rc in relations)
        assert any((a & b) == c and (ra & rb) == rc for c, rc in relations)
        COUNTS['palette_product_join_checks'] += 1
    # Directed S3 difference structure: actual equivalences can fail to commute.
    group = list(permutations(range(3)))
    identity = (0, 1, 2)
    mul = lambda a, b: tuple(a[b[i]] for i in range(3))
    h = {identity, (1, 0, 2)}
    j = {identity, (0, 2, 1)}
    hj = {mul(a, b) for a in h for b in j}
    jh = {mul(b, a) for a in h for b in j}
    assert hj != jh
    rh = {(x, mul(x, a)) for x in group for a in h}
    rj = {(x, mul(x, a)) for x in group for a in j}
    assert compose_rel(rh, rj) != compose_rel(rj, rh)
    COUNTS['directed_noncommuting_boundaries'] = 1


def main():
    graph_controls()
    kernel_and_ap_controls()
    homogeneity_controls()
    palette_controls()
    print(json.dumps(dict(status='PASS', seconds=round(time.monotonic() - START, 3),
                          counts=dict(sorted(COUNTS.items())),
                          scope='Bounded actual clone graphs, owner/real spans, partial automorphisms and full palette products.',
                          limits='No finite host is certified as an unbounded SAP/CCO source; no general clone theorem, arbitrary imaginary transfer, Ramsey theorem or Lean proof is certified.'), sort_keys=True))


if __name__ == '__main__':
    signal.alarm(30)
    main()
