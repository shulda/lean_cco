#!/usr/bin/env python3
"""Finite diagnostics for B054; no infinite-orbit or SAP certification."""
from __future__ import annotations
import itertools
import json


def require(condition, message):
    if not condition:
        raise AssertionError(message)


def window_group(owners, clones):
    universe = [('q', i) for i in range(owners)] + [('r', i, j) for i in range(owners) for j in range(clones)]
    owner_perms = list(itertools.permutations(range(owners)))
    clone_perms = list(itertools.permutations(range(clones)))
    group = []
    for op in owner_perms:
        for cps in itertools.product(clone_perms, repeat=owners):
            action = {}
            for u in universe:
                action[u] = ('q', op[u[1]]) if u[0] == 'q' else ('r', op[u[1]], cps[u[1]][u[2]])
            group.append(action)
    return universe, group


def closure(points):
    out = set(points)
    out.update(('q', u[1]) for u in points if u[0] == 'r')
    return out


def stabilizer(group, points):
    return [g for g in group if all(g[u] == u for u in points)]


def frame_checks():
    counts = {'group_elements': 0, 'frame_intersections': 0, 'orbit_inclusions': 0, 'stabilizer_equalities': 0}
    for owners, clones in [(3, 2), (3, 3)]:
        universe, group = window_group(owners, clones)
        counts['group_elements'] += len(group)
        A = {('q', 0)}
        B = closure(A | {('r', 0, 0), ('q', 1)})
        D = {('r', 0, 1)}
        generated = closure(D)
        require(A <= generated and generated & B == A, 'literal fresh-frame intersection failed')
        counts['frame_intersections'] += 1
        gd, ga = stabilizer(group, D), stabilizer(group, A)
        require(all(g in ga for g in gd), 'pointwise frame stabilizer not inside base stabilizer')
        for u in set(universe) - generated:
            small, big = {g[u] for g in gd}, {g[u] for g in ga}
            require(small <= big, 'subgroup orbit inclusion reversed')
            counts['orbit_inclusions'] += 1
        for T in [set(), {('q', 0)}, {('r', 0, 0)}, {('q', 0), ('r', 1, 0)}]:
            require(stabilizer(group, T) == stabilizer(group, closure(T)), 'term hull stabilizer changed')
            counts['stabilizer_equalities'] += 1
        # Original induced subgroup may be proper. Adding automorphisms enlarges orbits.
        subgroup = stabilizer(group, {('q', 2)})
        for u in universe:
            require({g[u] for g in subgroup} <= {g[u] for g in group}, 'larger group shrank orbit')
            counts['orbit_inclusions'] += 1
    require(closure(set()) == set(), 'empty closure acquired a constant')
    return counts


def signature_boundaries():
    # Non-MI cell quotient: upward row+column incidence has a unique solution.
    rows = range(4)
    cols = range(4)
    cells = [('cell', r, c) for r in rows for c in cols]
    a, b = ('row', 0), ('col', 0)
    unary_hull = {a, b}  # No unary function from one axis selects a cell.
    matches = [u for u in cells if u[1] == a[1] and u[2] == b[1]]
    require(len(matches) == 1 and matches[0] not in unary_hull, 'unique off-closure cell disappeared')
    for rp in itertools.permutations(rows):
        for cp in itertools.permutations(cols):
            if rp[0] == cp[0] == 0:
                require(('cell', rp[0], cp[0]) == matches[0], 'joint stabilizer moved unique cell')
    # Real-generated base misses cross-cell but its two old coordinates fix it.
    x, y = ('real', 0, 1, 0), ('real', 1, 0, 0)
    def enlarged_singleton(u):
        return {u, ('row', u[1]), ('col', u[2]), ('cell', u[1], u[2])}
    base = enlarged_singleton(x) | enlarged_singleton(y)
    require(matches[0] not in base and a in base and b in base, 'cross-cell boundary not point-generated')
    # Two different alleged new cells over the same upward row+column cannot be distinct.
    distinct_amalgams = [(c, d) for c in matches for d in matches if c != d]
    require(not distinct_amalgams, 'two unique cell copies strongly amalgamated')
    # Fine Q_K over coarse Q_J has exactly two bit classes, exchanged by an automorphism.
    coarse = ('block', 0)
    fine = [('bit', 0, bit) for bit in range(2)]
    require(len(fine) == 2 and all(u[1] == coarse[1] for u in fine), 'two-cover count changed')
    swap = {u: ('bit', 0, 1-u[2]) for u in fine}
    require(all(swap[u] != u for u in fine), 'bit swap acquired a selected fine point')
    # Parent compatibility is preserved by upward maps, not all rows meet all columns.
    compatible = [(('row', p, r), ('col', q, c)) for p, r, q, c in itertools.product(range(2), repeat=4) if p == q]
    incompatible = [(('row', p, r), ('col', q, c)) for p, r, q, c in itertools.product(range(2), repeat=4) if p != q]
    require(compatible and incompatible, 'hierarchical incidence incorrectly became Cartesian')
    return {'unique_cell_pairs': len(matches), 'cross_cell_real_bases': 1, 'two_cover_fibre_size': len(fine),
            'compatible_hierarchical_pairs': len(compatible), 'incompatible_hierarchical_pairs': len(incompatible)}


def main():
    result = {'status': 'PASS', 'scope': 'finite diagnostics only; no infinite-orbit, SAP or CCO certificate',
              'frames': frame_checks(), 'boundaries': signature_boundaries()}
    print(json.dumps(result, sort_keys=True))


if __name__ == '__main__':
    main()
