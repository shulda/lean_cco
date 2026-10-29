#!/usr/bin/env python3
"""Bounded B031 orbit-restriction and whole-packet diagnostics.

The positive model has real points (packet, owner-family, thin-position),
F-packets obtained by varying the last coordinate, actual E-owner classes
obtained by fixing the last two coordinates, and cyclic thin translations.
The ambient group is a common cyclic translation together with independent
packet permutations per owner family. Individual named owners are fixed,
not merely their union setwise. Full induced-union automorphisms are
computed independently from all permutations in the named owner cells,
filtering by the actual binary F relation.

Controls verify subgroup restriction and the CORRECT orbit inclusion,
G-invariant B giving full F-packet unions and restricted thin functions,
and finite packet bounds for stabilizer orbits over finite real A. The
empty owner set and empty real input are included. A non-invariant owner
set cuts a packet; a separate finite graph example has a STRICT ambient
restriction subgroup and STRICT orbit containment. That graph is a
structural countercheck, not a standing homogeneous orbital CCO source.

Crucial limit: in every finite real structure all points are algebraic,
even over the empty set. Thus the packet targets here are NOT finite-model
acl. These tests do not prove the infinite-source unary-closure theorem,
harmless-owner naming, homogeneity, CCO, EPPA or any HKN adapter.

Bounds: at most 12 real points, 6 owners, 216 owner-cell permutation
candidates; real parameter subsets have size <=2. The separate C8 graph
uses only its 16 explicit dihedral motions and 24 induced permutations.
No factorial search on all real points. Pilot timeout 10s; deadline 30s.
Reproduce: timeout 10s python tools/check_direct_owner_closure_controls.py
"""
from collections import Counter
from itertools import combinations, permutations, product
import json
import signal
import time


START = time.monotonic()


def require(ok, message, witness=None):
    if not ok:
        raise AssertionError((message, witness))


def tick():
    require(time.monotonic() - START < 30, '30-second diagnostic deadline')


def all_subsets(values, bound=None):
    # Flatten the size levels without constructing a large power set.
    values = tuple(values)
    for size in range(len(values) + 1 if bound is None else min(bound, len(values)) + 1):
        for c in combinations(values, size):
            yield frozenset(c)


def packet(point):
    return point[:2]


def owner(point):
    return point[1:]


def packet_saturation(points, real_set):
    chosen = {packet(x) for x in real_set}
    return frozenset(x for x in points if packet(x) in chosen)


def induced_group(points, named_owners, psize):
    """Compute FULL Aut of the finite F-structure with each owner named.

    Every such automorphism permutes packet labels within each named owner
    cell. Exhaust these candidates and retain exactly those preserving F.
    Owner labels also fix all cyclic-position differences and family names.
    """
    points = tuple(points)
    owners = tuple(sorted(named_owners))
    packet_perms = tuple(permutations(range(psize)))
    result = set()
    for choices in product(packet_perms, repeat=len(owners)):
        maps = dict(zip(owners, choices))
        image = tuple((maps[owner(x)][x[0]], x[1], x[2]) for x in points)
        if all((packet(x) == packet(y)) == (packet(u) == packet(v))
               for x, u in zip(points, image) for y, v in zip(points, image)):
            result.add(image)
    return result


def stabilizer(group, points, fixed):
    indices = {x: i for i, x in enumerate(points)}
    return tuple(g for g in group if all(g[indices[a]] == a for a in fixed))


def orbit(group, points, point):
    index = points.index(point)
    return frozenset(g[index] for g in group)


def packet_models(counts, witnesses):
    configurations = ((2, 1, 2), (2, 2, 2), (2, 1, 3), (2, 2, 3),
                      (3, 1, 2), (3, 1, 3))
    for psize, families, m in configurations:
        points = tuple(product(range(psize), range(families), range(m)))
        owners = tuple(product(range(families), range(m)))
        packet_perms = tuple(permutations(range(psize)))
        ambient = []
        for choices, shift in product(product(packet_perms, repeat=families), range(m)):
            ambient.append(tuple((choices[x[1]][x[0]], x[1], (x[2] + shift) % m)
                                 for x in points))
        require(len(set(ambient)) == len(ambient), 'explicit ambient motions are distinct')
        point_index = {x: i for i, x in enumerate(points)}
        counts['finite_packet_models'] += 1
        for B in all_subsets(owners):
            N = tuple(x for x in points if owner(x) in B)
            invariant = all({(f, (g + h) % m) for f, g in B} == set(B) for h in range(m))
            saturated = packet_saturation(points, N) == frozenset(N)
            require(invariant == saturated,
                    'G-invariant owner union is exactly a full F-packet union in this regular model')
            counts['owner_subset_saturation_checks'] += 1
            if invariant:
                counts['G_invariant_owner_unions'] += 1
                for h in range(m):
                    image = frozenset((p, f, (g + h) % m) for p, f, g in N)
                    require(image == frozenset(N), 'each literal thin translation restricts to the whole union')
                    counts['restricted_literal_thin_translations'] += 1
            if not B:
                require(not N, 'empty owners have empty real union')
                counts['empty_owner_unions'] += 1
            named_stabilizer = []
            for g in ambient:
                # Fix each named owner CLASS, including every real point in
                # that class setwise, rather than just preserving their union.
                if all(owner(g[point_index[x]]) == owner(x)
                       for x in points if owner(x) in B):
                    named_stabilizer.append(g)
            restriction = {tuple(g[point_index[x]] for x in N) for g in named_stabilizer}
            full_induced = induced_group(N, B, psize)
            require(restriction <= full_induced,
                    'ambient named-owner stabilizer restricts to an induced automorphism subgroup')
            counts['restriction_subgroup_inclusions'] += 1
            for A in all_subsets(N, bound=2):
                ambient_fixed = stabilizer(restriction, N, A)
                induced_fixed = stabilizer(full_induced, N, A)
                require(set(ambient_fixed) <= set(induced_fixed), 'parameter fixing survives restriction')
                target = packet_saturation(points, A)
                if invariant:
                    require(target <= frozenset(N), 'whole F[A] lies in the invariant owner union')
                if not A:
                    require(not target, 'F[empty] is empty')
                    counts['empty_real_inputs'] += 1
                    if N:
                        # Actual finite-model acl(empty) is N, NOT this empty target.
                        require(frozenset(N) != target, 'finite real acl cannot be identified with the packet target')
                        counts['finite_acl_empty_warning_witnesses'] += 1
                for x in N:
                    small = orbit(ambient_fixed, N, x)
                    large = orbit(induced_fixed, N, x)
                    require(small <= large, 'restriction orbit is contained in FULL induced-union orbit')
                    counts['parameter_orbit_inclusions'] += 1
                    if x in target:
                        representative = next(a for a in A if packet(a) == packet(x))
                        require(large <= frozenset(y for y in points if packet(y) == packet(representative)),
                                'the finite recognizable F-packet bounds the full stabilizer orbit')
                        require(len(large) <= m, 'finite packet orbit bound')
                        # Literal thin graphs are named; a translation of a fixed
                        # parameter is actually fixed in this stronger toy language.
                        h = (x[2] - representative[2]) % m
                        require((representative[0], representative[1], (representative[2] + h) % m) == x,
                                'every packet point is a literal thin translate of its parameter')
                        require(large == frozenset((x,)), 'named thin translations commute with parameter stabilizers')
                        counts['finite_packet_upper_orbit_bounds'] += 1
            tick()

        # Cut a genuine F-packet by retaining only one non-invariant owner.
        bad_B = frozenset(((0, 0),))
        bad_N = frozenset(x for x in points if owner(x) in bad_B)
        a = min(bad_N)
        missing = (a[0], a[1], (a[2] + 1) % m)
        require(missing in packet_saturation(points, (a,)) and missing not in bad_N,
                'non-invariant B can omit points of the complete F-packet')
        counts['negative_partial_packet_unions'] += 1
        witnesses.setdefault('partial_packet', {'B': sorted(bad_B), 'a': a,
                                                'missing_F_point': missing})


def strict_restriction_countercheck(counts, witnesses):
    # C8 with adjacency and its two parity owner classes. This deliberately
    # omits the complete orbital language and is NOT a standing source model.
    points = tuple(range(8))
    N = (0, 2, 4, 6)
    adjacency = lambda x, y: (x - y) % 8 in (1, 7)
    ambient = {tuple((sign * x + shift) % 8 for x in points)
               for sign, shift in product((1, -1), range(8))}
    require(len(ambient) == 16 and all(adjacency(x, y) == adjacency(g[x], g[y])
            for g in ambient for x, y in product(points, repeat=2)), 'actual C8 dihedral motions')
    owner_fixed = {g for g in ambient if all((g[x] % 2) == (x % 2) for x in points)}
    restrictions = {tuple(g[x] for x in N) for g in owner_fixed}
    full_induced = {p for p in permutations(N) if all(adjacency(x, y) == adjacency(u, v)
                    for x, u in zip(N, p) for y, v in zip(N, p))}
    require(restrictions < full_induced, 'ambient image can be a STRICT subgroup of full induced automorphisms')
    fixed = frozenset((0,))
    small = orbit(stabilizer(restrictions, N, fixed), N, 4)
    large = orbit(stabilizer(full_induced, N, fixed), N, 4)
    require(small < large and not large <= small, 'reversed orbit inclusion is false')
    counts['negative_group_equality'] += 1
    counts['negative_reversed_orbit_inclusion'] += 1
    witnesses['strict_ambient_image'] = {'model': 'C8 graph; structural countercheck outside standing-source hypotheses',
        'named_owner': list(N), 'ambient_restriction_group_order': len(restrictions),
        'full_induced_group_order': len(full_induced), 'fixed_real_A': sorted(fixed),
        'point': 4, 'ambient_fixed_orbit': sorted(small), 'full_induced_fixed_orbit': sorted(large)}


def check():
    global START
    START = time.monotonic()
    signal.signal(signal.SIGALRM, lambda *_: (_ for _ in ()).throw(TimeoutError('30-second diagnostic limit')))
    signal.alarm(30)
    counts, witnesses = Counter(), {}
    packet_models(counts, witnesses)
    strict_restriction_countercheck(counts, witnesses)
    signal.alarm(0)
    return {'status': 'PASS', 'scope': 'bounded orbit-restriction, named-owner and whole-packet diagnostics',
            'counts': dict(sorted(counts.items())), 'witnesses': witnesses,
            'seconds': round(time.monotonic() - START, 3),
            'limits': 'Finite real acl(empty) is the whole finite structure. No infinite unary acl, harmless-owner naming, standing homogeneity, CCO, EPPA or HKN adapter is certified.'}


if __name__ == '__main__':
    print(json.dumps(check(), sort_keys=True))
