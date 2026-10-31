#!/usr/bin/env python3
"""Bounded diagnostics for B060; no unbounded SAP/CCO or Lean certificate."""
from itertools import product, combinations
import json


def main():
    # Two typed copies of a component/row/column owner system, with four
    # distinct actual clones in every cell. The component gives genuinely
    # incompatible row/column tuples, not only a Cartesian all-valid test.
    vertices = list(product(range(2), range(2), range(3), range(3), range(4)))
    by_sort = [[i for i, x in enumerate(vertices) if x[0] == s] for s in range(2)]

    def atom(x, y):
        if x == y:
            return None
        if x[1] != y[1]:
            return 4
        same_row, same_col = x[2] == y[2], x[3] == y[3]
        return 0 if same_row and same_col else 1 if same_row else 2 if same_col else 3

    colours = [[atom(x, y) for y in vertices] for x in vertices]
    # Compute singleton STRONG products directly from ACTUAL triples of
    # distinct formal points, independently of the later palette algebra.
    table = {}
    for s, u, t in product(range(2), repeat=3):
        raw = [[set() for _ in range(5)] for _ in range(5)]
        for x in by_sort[s]:
            for y in by_sort[u]:
                a = colours[x][y]
                if a is None:
                    continue
                for z in by_sort[t]:
                    b, c = colours[y][z], colours[x][z]
                    if b is not None and c is not None:
                        raw[a][b].add(c)
        table[s, u, t] = [[frozenset(v) for v in row] for row in raw]

    def mul(s, u, t, a, b):
        return frozenset().union(*(table[s, u, t][i][j] for i in a for j in b))

    singletons = {frozenset([i]) for i in range(5)}
    reachable = {(s, t): set(singletons) for s, t in product(range(2), repeat=2)}
    while True:
        additions = {(s, t): set() for s, t in reachable}
        for s, u, t in product(range(2), repeat=3):
            for a in reachable[s, u]:
                for b in reachable[u, t]:
                    c = mul(s, u, t, a, b)
                    if c:
                        additions[s, t].add(c)
        changed = False
        for key, vals in additions.items():
            new = vals - reachable[key]
            if new:
                changed = True
                reachable[key].update(new)
        if not changed:
            break
    exact = {key: set(vals) | {frozenset(range(5))} for key, vals in reachable.items()}
    while True:
        changed = False
        for vals in exact.values():
            new = {a & b for a in vals for b in vals if a & b} - vals
            if new:
                vals.update(new)
                changed = True
        if not changed:
            break

    meet_checks = 0
    for s, u, t in product(range(2), repeat=3):
        for a in exact[s, u]:
            for b in exact[s, u]:
                if not a & b:
                    continue
                for c in exact[u, t]:
                    assert mul(s, u, t, a & b, c) == mul(s, u, t, a, c) & mul(s, u, t, b, c)
                    meet_checks += 1
        for a in exact[u, t]:
            for b in exact[u, t]:
                if not a & b:
                    continue
                for c in exact[s, u]:
                    assert mul(s, u, t, c, a & b) == mul(s, u, t, c, a) & mul(s, u, t, c, b)
                    meet_checks += 1

    def coordinates(x):
        s, g, r, c = x[:4]
        return (s, 'row', g, r), (s, 'col', g, c)

    coordinates_all = sorted({b for x in vertices for b in coordinates(x)})

    def in_class(x, b):
        return x[0] == b[0] and x[1] == b[2] and x[2 if b[1] == 'row' else 3] == b[3]

    reps = {b: [i for i, x in enumerate(vertices) if in_class(x, b)] for b in coordinates_all}
    spectra = {}
    for b in coordinates_all:
        for d in coordinates_all:
            spectra[b, d] = frozenset(colours[x][y] for x in reps[b] for y in reps[d] if x != y)

    jrow, jcol = frozenset([0, 1]), frozenset([0, 2])
    kernels = {'row': jrow, 'col': jcol}
    assert jrow & jcol == frozenset([0])
    diagonal_checks = 0
    for b in coordinates_all:
        assert spectra[b, b] == kernels[b[1]]
        diagonal_checks += 1

    tuple_checks = invalid_tuples = 0
    for s in range(2):
        rows = [b for b in coordinates_all if b[:2] == (s, 'row')]
        cols = [b for b in coordinates_all if b[:2] == (s, 'col')]
        for row, col in product(rows, cols):
            compatible = 0 in spectra[row, col]
            owners = {vertices[x][:4] for x in set(reps[row]) & set(reps[col])}
            assert compatible == bool(owners)
            assert len(owners) == (1 if compatible else 0)
            tuple_checks += 1
            invalid_tuples += not compatible

    owners = sorted({x[:4] for x in vertices})
    recovery_checks = mixed_checks = coincident_checks = 0
    for q, r in product(owners, repeat=2):
        s, t = q[0], r[0]
        a = atom(q + (0,), r + (1,))
        assert a is not None
        joint = frozenset(range(5))
        for b, d in product(coordinates(q), coordinates(r)):
            expected = mul(s, s, t, kernels[b[1]], frozenset([a]))
            expected = mul(s, t, t, expected, kernels[d[1]])
            assert spectra[b, d] == expected
            joint &= spectra[b, d]
            mixed_checks += 1
            coincident_checks += b == d
        assert joint == frozenset([a])
        assert mul(s, t, t, mul(s, s, t, frozenset([0]), frozenset([a])), frozenset([0])) == joint
        if s == t:
            assert (q == r) == (joint == frozenset([0]))
        recovery_checks += 1

    # FULL c;c retains equal real endpoints; STRONG composition does not.
    raw_pairs = strong_pairs = 0
    for s in range(2):
        for x in by_sort[s]:
            for z in by_sort[s]:
                raw = any(colours[x][y] == 0 and colours[y][z] == 0 for y in by_sort[s])
                assert raw == (vertices[x][:4] == vertices[z][:4])
                raw_pairs += raw
                strong_pairs += raw and x != z
        assert mul(s, s, s, frozenset([0]), frozenset([0])) == frozenset([0])
    assert raw_pairs > strong_pairs

    # Actual elementary-abelian free actions. A rigid same-object arrow
    # occurring on a triangle with one repeated pair atom is idempotent,
    # hence identity. Then ANY same desired child seed passes every pair.
    character_checks = seed_checks = clique_prefixes = 0
    for dim in range(1, 4):
        group = range(1 << dim)
        for char in range(1, 1 << dim):
            chi = lambda g: (char & g).bit_count() % 2
            for g in group:
                assert ((g ^ g) == g) == (g == 0)
                if (g ^ g) == g:
                    assert chi(g) == 0
                character_checks += 1
            for n in range(1, 7):
                # Distinct action orbits model nonrigid parent pairs;
                # repeated group points model rigid identity cylinders.
                for epsilon in (0, 1):
                    prescribed = {(orbit, 0): epsilon for orbit in range(n)}
                    extended = {(orbit, g): epsilon ^ chi(g) for orbit in range(n) for g in group}
                    assert all(extended[x] == bit for x, bit in prescribed.items())
                    for orbit in range(n):
                        for a, b in product(group, repeat=2):
                            assert extended[orbit, a] ^ extended[orbit, b] == chi(a ^ b)
                            seed_checks += 1
                    # The n marked owners each retain all four clones.
                    clone_points = [(owner, clone) for owner in range(n) for clone in range(4)]
                    assert all(epsilon == prescribed[owner, 0] for owner, clone in clone_points)
                    assert len({owner for owner, clone in clone_points}) == n
                    clique_prefixes += 1

    # Bare row equivalences omit column/fine-colour information: two
    # pairs with the same row coordinate pattern have different atoms.
    x = (0, 0, 0, 0, 0)
    y, z = (0, 0, 1, 0, 0), (0, 0, 1, 1, 0)
    assert coordinates(y)[0] == coordinates(z)[0]
    assert atom(x, y) != atom(x, z)
    # Clone-constant arbitrary unary marking may pick just ONE owner.
    chosen = owners[0]
    labels = {x: x[:4] == chosen for x in vertices}
    assert sum(labels.values()) == 4
    assert {x[:4] for x in vertices if labels[x]} == {chosen}
    assert all(len({labels[x] for x in vertices if x[:4] == q}) == 1 for q in owners)

    # Optional MI boundary: this checks transverse coordinates in one V4
    # packet. In the INFINITE packet family, proper F has only Top above it.
    group = set(range(4))
    subgroups = [frozenset(h) for mask in range(1, 16)
                 if 0 in (h := {g for g in group if mask & (1 << g)})
                 and all(a ^ b in h for a in h for b in h)]
    assert frozenset([0, 1]) in subgroups and frozenset([0, 2]) in subgroups
    assert frozenset([0, 1]) & frozenset([0, 2]) == frozenset([0])
    assert len(subgroups) == 5
    # After all phase labels are named, every same-sort finite packet
    # has exactly one owner, although it still has four real clones.
    packet_separations = 0
    for phase in group:
        for component in range(2):
            packet_owners = [(component, bit) for bit in group]
            child_owners = [q for q in packet_owners if q[1] == phase]
            assert len(child_owners) == 1
            packet_separations += 1
    print(json.dumps(dict(status='PASS_FINITE_DIAGNOSTICS_ONLY', vertices=len(vertices), actual_owners=len(owners), hidden_coordinates=len(coordinates_all), nonempty_exact_domains={str(k): len(v) for k,v in exact.items()}, nonempty_meet_products=meet_checks, tuple_domains=tuple_checks, incompatible_tuples=invalid_tuples, hidden_diagonals=diagonal_checks, mixed_spectrum_products=mixed_checks, coincident_coordinate_cases=coincident_checks, singleton_recoveries=recovery_checks, full_clone_pairs=raw_pairs, strong_clone_pairs=strong_pairs, rigid_character_checks=character_checks, finite_seed_equations=seed_checks, growing_owner_prefixes=clique_prefixes, finite_packet_subgroups=len(subgroups), terminal_packet_separations=packet_separations), sort_keys=True))


if __name__ == '__main__':
    main()
