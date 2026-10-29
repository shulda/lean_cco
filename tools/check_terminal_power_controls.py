#!/usr/bin/env python3
"""Bounded B032 parity, actual orbital and positive-walk diagnostics.

All simple graphs on <=5 vertices are checked by TWO independent methods:
parity-lift BFS and Boolean powers of the adjacency relation. Actual finite
dihedral actions on cycles (and two disjoint cycle copies) supply transitive
orbital models. Their pair orbits are enumerated, the edge relation is one
genuine diversity orbital, and actual even-walk versus connectivity classes
have relative index exactly two in every bipartite nontrivial component.

Nonbipartite components have walks of both parities. Shortest parity walks
give a constructive common threshold; two-edge backtracks pad each to the
required length. Boolean relation powers independently check the threshold,
and connectivity composed with adjacency is a fixed point once all lengths
are available. This tests represented walks, NOT the theorem's SAP step.

FINITE graphs are not being asserted to satisfy SAP. C3 explicitly has long
represented walks but no injective 3-edge path. Bounded complete hosts with
enough vertices check only literal pinned-endpoint path certificates. They
do not prove general SAP injectivisation or eventual STRONG saturation.
RAW even connectivity uses an empty walk for reflexivity; the positive power
API rejects exponent zero, and diversity outputs exclude equality.

Bounds: 1,099 simple graphs, at most 18 points in an actual orbital model,
36 explicit group permutations, positive powers to <=2|V| past a computed
threshold, and seven complete-host path certificates. No factorial group
search. Normal timeout 10s; SIGALRM/deadline 30s. Reproduce:
  timeout 10s python tools/check_terminal_power_controls.py

No infinite source, SAP, homogeneity, FULL NR2, CCO, eventual STRONG profile,
EPPA or coherent extension theorem is certified by these finite controls.
"""
from collections import Counter, deque
from itertools import combinations
import json
import signal
import time


START = time.monotonic()


def require(ok, message, witness=None):
    if not ok:
        raise AssertionError((message, witness))


def tick():
    require(time.monotonic() - START < 30, '30-second diagnostic deadline')


def adjacency(n, edges):
    out = [set() for _ in range(n)]
    for x, y in edges:
        require(x != y, 'simple graph has a loop')
        out[x].add(y)
        out[y].add(x)
    return tuple(frozenset(v) for v in out)


def relation(adj):
    return frozenset((x, y) for x, row in enumerate(adj) for y in row)


def compose(left, right):
    rows = {}
    for x, y in right:
        rows.setdefault(x, set()).add(y)
    return frozenset((x, z) for x, y in left for z in rows.get(y, ()))


def positive_power(adj, exponent):
    if type(exponent) is not int or exponent < 1:
        raise ValueError('Only POSITIVE represented powers are accepted')
    base = result = relation(adj)
    for _ in range(exponent - 1):
        result = compose(result, base)
    return result


def parity_walks(adj, start):
    """Independent BFS in V x {even,odd}, retaining actual path witnesses."""
    paths = {(start, 0): (start,)}
    pending = deque([(start, 0)])
    while pending:
        x, parity = pending.popleft()
        for y in adj[x]:
            state = (y, 1 - parity)
            if state not in paths:
                paths[state] = paths[(x, parity)] + (y,)
                pending.append(state)
    return paths


def walk_ok(adj, walk):
    return bool(walk) and all(y in adj[x] for x, y in zip(walk, walk[1:]))


def connectivity(adj):
    result = set()
    for x in range(len(adj)):
        reached = {x}
        pending = [x]
        while pending:
            y = pending.pop()
            for z in adj[y] - reached:
                reached.add(z)
                pending.append(z)
        result.update((x, y) for y in reached)
    return frozenset(result)


def equivalence(rel, vertices):
    return (all((x, x) in rel for x in vertices)
            and all((y, x) in rel for x, y in rel)
            and compose(rel, rel) <= rel)


def is_bipartite(adj, component):
    colours = {}
    for start in component:
        if start in colours:
            continue
        colours[start] = 0
        pending = [start]
        while pending:
            x = pending.pop()
            for y in adj[x]:
                if y not in colours:
                    colours[y] = 1 - colours[x]
                    pending.append(y)
                elif colours[y] == colours[x]:
                    return False
    return True


def padded_walk(adj, base, length):
    gap = length - (len(base) - 1)
    require(gap >= 0 and gap % 2 == 0, 'bad parity padding')
    if not gap:
        return base
    x = base[0]
    require(adj[x], 'padding needs one actual neighbour')
    neighbour = min(adj[x])
    walk = (x,) + (neighbour, x) * (gap // 2) + base[1:]
    require(len(walk) - 1 == length and walk_ok(adj, walk), 'padding certificate')
    return walk


def analyse_graph(adj, counts, exhaustive=False):
    n = len(adj)
    vertices = tuple(range(n))
    conn = connectivity(adj)
    paths = [parity_walks(adj, x) for x in vertices]
    even = frozenset((x, y) for x in vertices for y in vertices if (y, 0) in paths[x])
    require(equivalence(conn, vertices), 'connectivity equivalence')
    require(equivalence(even, vertices) and even <= conn, 'even equivalence')
    seen = set()
    for x in vertices:
        if x in seen:
            continue
        component = frozenset(y for y in vertices if (x, y) in conn)
        seen.update(component)
        classes = {frozenset(y for y in component if (z, y) in even) for z in component}
        bip = is_bipartite(adj, component)
        expected = 2 if bip and adj[x] else 1
        require(len(classes) == expected, 'actual even-class relative index', component)
        counts['bipartite_index_two_components' if expected == 2 else 'index_one_components'] += 1
        if not bip:
            for z in component:
                require(all((y, p) in paths[z] for y in component for p in (0, 1)),
                        'nonbipartite component missing one walk parity')
            threshold = max(len(paths[z][(y, p)]) - 1
                            for z in component for y in component for p in (0, 1))
            require(threshold >= 1, 'positive threshold')
            for length in range(threshold, threshold + 3):
                power = positive_power(adj, length)
                require(all((z, y) in power for z in component for y in component),
                        'BFS common threshold disagrees with Boolean powers')
                for z in component:
                    for y in component:
                        certificate = padded_walk(adj, paths[z][(y, length % 2)], length)
                        require(certificate[0] == z and certificate[-1] == y, 'pinned endpoints')
                        counts['constructive_padded_walks'] += 1
            counts['nonbipartite_components'] += 1
        elif adj[x]:
            # Walk parity remains tied to the two actual even classes.
            for length in range(1, 7):
                power = positive_power(adj, length)
                for z in component:
                    for y in component:
                        require(((z, y) in power) <= ((z, y) in even if length % 2 == 0
                                                     else (z, y) not in even),
                                'bipartite parity obstruction disappeared')
                        counts['bipartite_parity_guards'] += 1
    if exhaustive:
        counts['enumerated_simple_graphs'] += 1
    return conn, even, paths


def enumerate_small_graphs(counts):
    for n in range(1, 6):
        possible = tuple(combinations(range(n), 2))
        for mask in range(1 << len(possible)):
            edges = tuple(edge for bit, edge in enumerate(possible) if mask & (1 << bit))
            analyse_graph(adjacency(n, edges), counts, exhaustive=True)
        tick()


def cycle_model(size, copies):
    points = tuple((c, i) for c in range(copies) for i in range(size))
    number = {p: i for i, p in enumerate(points)}
    edges = [(number[(c, i)], number[(c, (i + 1) % size)])
             for c in range(copies) for i in range(size)]
    adj = adjacency(len(points), edges)
    group = set()
    for offset in range(copies):
        for shift in range(size):
            for sign in (-1, 1):
                group.add(tuple(number[((c + offset) % copies, (sign * i + shift) % size)]
                                for c, i in points))
    return adj, tuple(sorted(group))


def actual_orbital_models(counts):
    examples = []
    for size in range(3, 10):
        for copies in (1, 2):
            adj, group = cycle_model(size, copies)
            n = len(adj)
            require({g[0] for g in group} == set(range(n)), 'actual action not transitive')
            conn, even, paths = analyse_graph(adj, counts)
            edge = relation(adj)
            first = next(iter(edge))
            require({(g[first[0]], g[first[1]]) for g in group} == edge,
                    'edge is not one ACTUAL diversity pair orbital')
            # Check the distinct-endpoint readout at EVERY tested positive
            # length, including transient lengths before eventual saturation.
            for length in range(1, 2 * n + 1):
                raw = positive_power(adj, length)
                diversity = frozenset((x, y) for x, y in raw if x != y)
                oracle = frozenset((x, y) for x in range(n) for y in range(n)
                                   if x != y and (y, length % 2) in paths[x]
                                   and len(paths[x][(y, length % 2)]) - 1 <= length)
                require(diversity == oracle, 'all-positive endpoint readout failure')
                require(not any(x == y for x, y in diversity),
                        'positive represented diagonal became diversity')
                if any(x == y for x, y in raw):
                    counts['positive_RAW_diagonals_excluded_from_diversity'] += 1
                counts['all_positive_distinct_endpoint_readouts'] += 1
            remaining = {(x, y) for x in range(n) for y in range(n) if x != y and (x, y) in conn}
            orbits = []
            while remaining:
                pair = min(remaining)
                orbit = frozenset((g[pair[0]], g[pair[1]]) for g in group)
                require(orbit <= remaining, 'actual pair orbits not a partition')
                remaining.difference_update(orbit)
                orbits.append((pair, orbit))
            for g in group:
                require(all(((x, y) in even) == ((g[x], g[y]) in even)
                            and ((x, y) in conn) == ((g[x], g[y]) in conn)
                            for x in range(n) for y in range(n)),
                        'walk equivalences not invariant under actual source action')
            if size % 2:
                threshold = max(max(len(paths[x][(y, p)]) - 1 for p in (0, 1))
                                for (x, y), _ in orbits)
                require(threshold >= 1, 'common atom threshold not positive')
                for length in range(threshold, threshold + 2 * n + 1):
                    raw = positive_power(adj, length)
                    diversity = frozenset((x, y) for x, y in raw if x != y)
                    expected = frozenset((x, y) for x, y in conn if x != y)
                    require(diversity == expected, 'uniform actual-orbital threshold failure')
                    counts['uniform_positive_power_checks'] += 1
                for (x, y), orbit in orbits:
                    for length in (threshold, threshold + 1):
                        representative = padded_walk(adj, paths[x][(y, length % 2)], length)
                        for u, v in orbit:
                            motion = next(g for g in group if g[x] == u and g[y] == v)
                            moved = tuple(motion[z] for z in representative)
                            require(moved[0] == u and moved[-1] == v and walk_ok(adj, moved),
                                    'pair-orbit walk transport failed')
                            counts['actual_pair_orbit_transports'] += 1
                # Whole connectivity (with equality) is a fixed point for adjacency.
                require(compose(conn, edge) == conn, 'eventual relation fixed-point failure')
                examples.append({'cycle': size, 'copies': copies, 'threshold': threshold,
                                 'diversity_pair_orbits': len(orbits)})
            else:
                x, y = next(iter(edge))
                require((x, y) not in positive_power(adj, 2 * size), 'even bipartite failure missing')
                counts['negative_bipartite_saturation'] += 1
            counts['actual_transitive_orbital_models'] += 1
            counts['actual_connectivity_diversity_orbits'] += len(orbits)
            tick()
    return examples


def boundary_and_path_certificates(counts):
    triangle = adjacency(3, combinations(range(3), 2))
    for zero in (0, -1):
        try:
            positive_power(triangle, zero)
        except ValueError:
            counts['rejected_nonpositive_powers'] += 1
        else:
            raise AssertionError('accepted a nonpositive power')
    raw_two = positive_power(triangle, 2)
    require(all((x, x) in raw_two for x in range(3)), 'RAW two-step equality witness')
    diversity_two = {(x, y) for x, y in raw_two if x != y}
    require(not any(x == y for x, y in diversity_two), 'logical equality became diversity')
    counts['negative_equality_as_diversity'] += 1
    require((0, 1) in positive_power(triangle, 3), 'long represented walk missing')
    require(4 > len(triangle), 'finite-host path counterexample')
    counts['negative_walk_implies_injective_path_without_SAP'] += 1
    for length in range(1, 8):
        adj = adjacency(length + 1, combinations(range(length + 1), 2))
        injective = (0,) + tuple(range(2, length + 1)) + (1,)
        require(len(injective) - 1 == length and len(set(injective)) == len(injective),
                'bounded injective certificate not a path')
        require(injective[0] == 0 and injective[-1] == 1 and walk_ok(adj, injective),
                'bounded pinned diversity path invalid')
        counts['bounded_complete_host_pinned_paths'] += 1
    return {'raw_equality_walk': [0, 1, 0],
            'finite_no_SAP_counterexample': {'graph': 'C3', 'walk': [0, 1, 0, 1],
                                           'injective_3_edge_path_requires': 4, 'host_points': 3},
            'nonpositive_STRONG_power': 'excluded',
            'endpoint_guard': 'all target diversity pairs have distinct literal endpoints'}


def main():
    signal.signal(signal.SIGALRM, lambda *_: (_ for _ in ()).throw(TimeoutError('30s deadline')))
    signal.alarm(30)
    counts = Counter()
    enumerate_small_graphs(counts)
    examples = actual_orbital_models(counts)
    witnesses = boundary_and_path_certificates(counts)
    tick()
    signal.alarm(0)
    return {'status': 'PASS',
            'scope': 'bounded graph parity, actual orbital transport and positive-walk diagnostics',
            'counts': dict(sorted(counts.items())),
            'witnesses': dict(witnesses, uniform_cycle_thresholds=examples),
            'limits': 'Finite graph controls do not certify SAP, FULL NR2, homogeneity, infinite sources, STRONG injectivisation or eventual STRONG saturation; CCO is not used.',
            'seconds': round(time.monotonic() - START, 3)}


if __name__ == '__main__':
    print(json.dumps(main(), sort_keys=True))
