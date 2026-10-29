#!/usr/bin/env python3
"""Bounded B030 rank/phase and joint-owner assembly diagnostics, NOT EPPA proofs.

Rank model: S3^d acts coordinatewise on {0,1,2}^d, 0<=d<=3. Actual pair
orbits are computed from permutation generators, not postulated colour
counts. Every nonempty coordinate-collapse kernel K is genuinely RAW
exact: its all-changed-coordinate diversity atom squared is K, including
equality. Induced quotient actions and their diversity pair orbits are
recomputed. Identity quotients are checked separately and do not decrease
rank. These are finite group models, not claimed infinite CCO sources.

Phase model: all P/O/U dependency nodes at ranks <=5. Lower-rank P/O/U,
same-rank O->P and U->O calls decrease the lexicographic (rank,phase)
measure. Injected same-rank P->U recursion creates a concrete cycle;
higher-rank calls fail even when their phase is smaller.

Owner model: B_Omega={0,1,2}^3; B_i forgets coordinate i. All three
overlapping pair-coordinate projections are retained. The finite master
is exactly the compatible tuple set. S3^3 projects onto Aut(B_i), with a
fibre-transitive kernel. Factor points add an independent 3-point packet.
The root calculation fixes an entire exceptional action, chooses ONE
joint lift and transports to ONE actual old source point. Negative cases
show missing master tuples, matching only a root, and choosing unrelated
old projected targets are insufficient.

Search bounds: <=27 rank-model points, <=729 ordered pairs per model;
six rank levels; 27 master owners, 27 packet positions; 26,244 literal
root transports. No arbitrary permutation enumeration, colour relabeling
or imported control script. Pilot timeout 10s; full SIGALRM limit 30s.
Reproduce: timeout 10s python tools/check_rank_induction_controls.py

No infinite acl, actual source inheritance, safe selector, HKN, strong
closed amalgamation, rooted/ordinary EPPA or coherent action is certified.
The packet-closure targets below are combinatorial, not acl in a finite
structure, where all points would be algebraic.
"""
from collections import Counter
from itertools import combinations, permutations, product
import json
import signal
import time


START = time.monotonic()
S3 = tuple(permutations(range(3)))


def require(ok, message, witness=None):
    if not ok:
        raise AssertionError((message, witness))


def tick():
    require(time.monotonic() - START < 30, '30-second diagnostic deadline')


def pair_orbits(points, generators):
    pending = set(product(points, repeat=2))
    classes = []
    while pending:
        seed = min(pending)
        orbit, stack = {seed}, [seed]
        while stack:
            x, y = stack.pop()
            for g in generators:
                image = g[x], g[y]
                if image not in orbit:
                    orbit.add(image)
                    stack.append(image)
        require(orbit <= pending, 'generated pair orbits partition the actual pair set')
        pending.difference_update(orbit)
        classes.append(frozenset(orbit))
    return tuple(classes)


def compose_relations(left, right, points):
    rows = {x: {z for y, z in right if y == x} for x in points}
    return frozenset((x, z) for x, y in left for z in rows[y])


def rank_controls(counts, witnesses):
    for d in range(4):
        points = tuple(product(range(3), repeat=d))
        generators = []
        for axis in range(d):
            for p in ((1, 0, 2), (0, 2, 1)):
                generators.append({x: x[:axis] + (p[x[axis]],) + x[axis + 1:] for x in points})
        orbits = pair_orbits(points, generators)
        diagonal = frozenset((x, x) for x in points)
        require(diagonal in orbits, 'one real equality orbital: actual transitivity')
        diversity = tuple(o for o in orbits if o != diagonal)
        require(len(diversity) == 2**d - 1, 'actual diversity orbit count')
        require(all(frozenset((y, x) for x, y in o) == o for o in orbits),
                'all actual named pair orbitals are symmetric')
        counts['actual_pair_orbit_models'] += 1
        for collapsed_mask in range(1 << d):
            retained = tuple(i for i in range(d) if not collapsed_mask & (1 << i))
            pi = {x: tuple(x[i] for i in retained) for x in points}
            quotient = tuple(sorted(set(pi.values())))
            induced = []
            for g in generators:
                qmap = {}
                for x in points:
                    require(pi[x] not in qmap or qmap[pi[x]] == pi[g[x]], 'actual quotient action well-defined')
                    qmap[pi[x]] = pi[g[x]]
                induced.append(qmap)
            q_orbits = pair_orbits(quotient, induced)
            q_diagonal = frozenset((q, q) for q in quotient)
            q_rank = len(q_orbits) - 1
            orbit_images = {frozenset((pi[x], pi[y]) for x, y in o) for o in orbits}
            require(orbit_images == set(q_orbits), 'every actual quotient orbital is an actual original orbital image')
            kernel = frozenset((x, y) for x, y in product(points, repeat=2) if pi[x] == pi[y])
            if collapsed_mask:
                atom = frozenset((x, y) for x, y in product(points, repeat=2)
                                 if all((x[i] != y[i]) == bool(collapsed_mask & (1 << i)) for i in range(d)))
                require(atom in diversity, 'collapsed-coordinate profile is ONE actual diversity atom')
                require(compose_relations(atom, atom, points) == kernel,
                        'nonidentity quotient kernel is genuinely RAW exact, including equality')
                require(frozenset((pi[x], pi[y]) for x, y in atom) == q_diagonal,
                        'at least one original diversity orbital becomes real quotient equality')
                require(q_rank < len(diversity), 'strict rank decrease for actual nonidentity exact quotient',
                        (d, collapsed_mask, len(diversity), q_rank))
                counts['strict_exact_quotient_rank_decreases'] += 1
            else:
                require(q_rank == len(diversity), 'identity quotient is NOT a strict recursion step')
                counts['identity_quotients_not_strict'] += 1
            counts['actual_quotient_pair_orbit_checks'] += 1
        tick()
    witnesses['rank_boundary'] = {'zero_diversity_source_points': 1,
                                  'nonidentity_example': {'source_diversity': 7, 'quotient_diversity': 3},
                                  'identity_quotient_does_not_decrease': True}


def dependency_order(graph):
    pending = {node: set(deps) for node, deps in graph.items()}
    order = []
    while pending:
        ready = sorted(n for n, deps in pending.items() if not deps)
        if not ready:
            return None
        order.extend(ready)
        for n in ready:
            del pending[n]
        for deps in pending.values():
            deps.difference_update(ready)
    return order


def phase_controls(counts, witnesses):
    phase = {'P': 0, 'O': 1, 'U': 2}
    measure = lambda node: (node[0], phase[node[1]])
    graph = {}
    for n in range(6):
        graph[n, 'P'] = {(m, p) for m in range(n) for p in phase}
        graph[n, 'O'] = {(n, 'P')}
        graph[n, 'U'] = {(m, 'O') for m in range(n + 1)}
    require(dependency_order(graph) is not None, 'all bounded phased obligations are acyclic')
    for caller, deps in graph.items():
        for provider in deps:
            require(measure(provider) < measure(caller), 'every provider decreases (rank,phase)', (caller, provider))
            counts['strict_phase_dependency_edges'] += 1
    for n in range(6):
        bad = {node: set(deps) for node, deps in graph.items()}
        bad[n, 'P'].add((n, 'U'))
        require(not measure((n, 'U')) < measure((n, 'P')) and dependency_order(bad) is None,
                'same-rank U inside P creates P->U->O->P recursion')
        counts['negative_same_rank_master_cycles'] += 1
        if n < 5:
            require(not measure((n + 1, 'P')) < measure((n, 'U')),
                    'a smaller phase never excuses a larger actual quotient rank')
            counts['negative_rank_increase_despite_lower_phase'] += 1
    counts['phase_nodes'] = len(graph)
    witnesses['same_rank_cycle'] = ['P_n calls U_n', 'U_n calls O_n', 'O_n calls P_n']
    tick()


def owner_projection(point, i):
    return tuple(point[j] for j in range(3) if j != i)


def compatible(owners):
    values = [{} for _ in range(3)]
    for i, pair in enumerate(owners):
        values[i] = dict(zip((j for j in range(3) if j != i), pair))
    return all(values[i][axis] == values[j][axis]
               for i, j in combinations(range(3), 2) for axis in values[i].keys() & values[j].keys())


def joint_owner_controls(counts, witnesses):
    for p in S3:
        for x, y in product(range(3), repeat=2):
            require((x == y) == (p[x] == p[y]), 'actual component action preserves its full fine equality colour')
            counts['actual_fine_coordinate_colour_checks'] += 1
    master = tuple(product(range(3), repeat=3))
    owners = tuple(product(range(3), repeat=2))
    compatible_tuples = {t for t in product(owners, repeat=3) if compatible(t)}
    actual_tuples = {tuple(owner_projection(x, i) for i in range(3)) for x in master}
    require(compatible_tuples == actual_tuples and len(compatible_tuples) == 27,
            'the SAME finite master is exactly the FULL compatible owner set')
    for i in range(3):
        require({owner_projection(x, i) for x in master} == set(owners), 'each actual owner projection is onto')
        for x, y in product(master, repeat=2):
            if owner_projection(x, i) == owner_projection(y, i):
                require(any(p[x[i]] == y[i] for p in S3), 'actual projection kernel is transitive on every fibre')
                counts['joint_owner_kernel_point_cases'] += 1
    missing = (2, 2, 2)
    incomplete = set(master) - {missing}
    require(all({owner_projection(x, i) for x in incomplete} == set(owners) for i in range(3)),
            'all owner projections can remain onto after one master tuple is removed')
    require(tuple(owner_projection(missing, i) for i in range(3)) not in
            {tuple(owner_projection(x, i) for i in range(3)) for x in incomplete},
            'surjective projections alone permit a phantom compatible owner tuple')
    counts['negative_incomplete_master'] += 1
    witnesses['phantom_owner_tuple'] = {'missing_actual_master_point': missing, 'all_three_projections_still_onto': True}

    # Entire compatible actions, not only their values at the chosen root.
    root = (0, 0, 0)
    bad_actions = [((0, 1, 2), (0, 1, 2)),
                   ((0, 1, 2), (0, 1, 2)),
                   ((0, 1, 2), (0, 2, 1))]
    act = lambda pair, action: tuple(p[x] for p, x in zip(action, pair))
    require(all(act(owner_projection(root, i), bad_actions[i]) == owner_projection(root, i) for i in range(3)),
            'independent owner actions can agree at the chosen root')
    require(any(not compatible(tuple(act(owner_projection(x, i), bad_actions[i]) for i in range(3))) for x in master),
            'root-only agreement does NOT give one entire compatible joint-owner action')
    counts['negative_singleton_only_owner_agreement'] += 1

    old = ((1, 0, 0), (0, 1, 0), (0, 0, 1))
    require(root not in old and all(owner_projection(root, i) in {owner_projection(a, i) for a in old} for i in range(3)),
            'compatible old projected roots need NOT assemble to an actual old source point')
    counts['negative_independent_old_root_targets'] += 1
    witnesses['old_coordinate_targets_not_one_old_root'] = {'old_joint_points': old, 'assembled_nonold_root': root}

    packet_target = (2, 1, 0)  # Literal noncanonical original target.
    for z, a, exceptional in product(master, old, range(3)):
        retained = tuple(j for j in range(3) if j != exceptional)
        prescribed_actions = tuple(product(*(tuple(p for p in S3 if p[z[j]] == a[j]) for j in retained)))
        for prescribed in prescribed_actions:
            full = [None] * 3
            for axis, action in zip(retained, prescribed):
                full[axis] = action
            full[exceptional] = next(p for p in S3 if p[z[exceptional]] == a[exceptional])
            require(tuple(full[j] for j in retained) == prescribed and tuple(full[j][z[j]] for j in range(3)) == a,
                    'ONE joint lift preserves ENTIRE exceptional action and hits ONE original joint owner')
            counts['prescribed_exceptional_joint_owner_lifts'] += 1
            for packet_root in master:
                fine_actions = tuple(next(p for p in S3 if p[packet_root[j]] == packet_target[j]) for j in range(3))
                image_root = tuple(full[j][z[j]] for j in range(3)) + tuple(fine_actions[j][packet_root[j]] for j in range(3))
                require(image_root == a + packet_target, 'factor transports hit the LITERAL selected old real point')
                # The entire finite unsafe packet clique, not just its root.
                image_clique = {tuple(full[j][z[j]] for j in range(3)) + tuple(fine_actions[j][u[j]] for j in range(3))
                                for u in master}
                require(image_clique == {a + u for u in master}, 'the whole packet clique enters one closed target packet')
                counts['literal_root_and_whole_packet_transports'] += 1
        tick()
    counts['full_compatible_master_points'] = len(master)
    witnesses['literal_root_target_packet'] = packet_target


def check():
    global START
    START = time.monotonic()
    signal.signal(signal.SIGALRM, lambda *_: (_ for _ in ()).throw(TimeoutError('30-second diagnostic limit')))
    signal.alarm(30)
    counts, witnesses = Counter(), {}
    rank_controls(counts, witnesses)
    phase_controls(counts, witnesses)
    joint_owner_controls(counts, witnesses)
    signal.alarm(0)
    return {'status': 'PASS', 'scope': 'bounded actual-orbit rank, phased dependency and joint-owner/root diagnostics',
            'counts': dict(sorted(counts.items())), 'witnesses': witnesses,
            'seconds': round(time.monotonic() - START, 3),
            'limits': 'No infinite source/acl/CCO/closed-SAP/HKN/EPPA or coherence certification.'}


if __name__ == '__main__':
    print(json.dumps(check(), sort_keys=True))
