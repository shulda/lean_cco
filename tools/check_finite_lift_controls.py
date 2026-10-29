#!/usr/bin/env python3
"""Bounded B029 finite exact/rooted reconstruction diagnostics; NOT EPPA proofs.

Representation/preflight: two labelled 3x3 grids, points (i,a,b), a,b<3.
Fine colours are equality, the THREE within-grid coordinate equality
patterns, and one outside-grid atom. K=(same i,a), H=(same i,b) are
nonnested. They are GENUINELY RAW-word exact: the square of within-K
(respectively within-H) diversity is the full K (respectively H) relation,
including real equality. K;H is their join F=(same grid). Fibre size three
is essential; a thin difference table would not establish this exactness.

All real automorphisms have structured form grid permutation followed by
one S3 permutation of each coordinate in each grid: 2!*(3!)^4=2,592 maps,
not 18! arbitrary bijections. Quotient and owner groups each have 72 maps;
coarse group has two. Literal fine-colour preservation and actual induced
quotient maps are checked. Bounded source: all <=34 partial maps of one
three-point L-shape. All 63 nonempty quotient subsets and their FULL real
preimages are checked. Root tests use every clique of size <=3 inside a
nine-point grid plus the entire grid, with EVERY selected point, every
compatible ENTIRE quotient action and every compatible ENTIRE owner lift.

Space: <=5 raw orbit relations on 18 points; <=72^2 quotient-action pairs;
<=684 selected-root inputs and <=98,496 relative root lifts; 3,888 prescribed
point/conjugation cases. Fixed names, no colour/symmetry relabeling search.
Expected runtime <10s. Pilot: timeout 10s. Full SIGALRM/phase limit: 30s.
All finite witnesses/counts go to one JSON checkpoint; assertions carry a
counterexample. Reproduce from manuscript root:
  timeout 10s python tools/check_finite_lift_controls.py > /tmp/b029-controls.json

Finite grid models are NOT claimed CCO or infinite source models. F[-]
below is a finite packet-closure operator, NOT algebraic closure of a finite
structure (where all points are algebraic). Its coordinate identity is only
a reconstruction diagnostic. No infinite acl, ambient-lifting theorem,
closed-SAP, ordinary/relative EPPA, group section or coherence is certified.
No other control script is imported.
"""
from collections import Counter
from itertools import combinations, permutations, product
import json
import signal
import time

START = time.monotonic()
POINTS = tuple(product(range(2), range(3), range(3)))
QINDEX = {x: i for i, x in enumerate(POINTS)}
AXES = tuple(product(range(2), range(3)))
AINDEX = {x: i for i, x in enumerate(AXES)}
S3 = tuple(permutations(range(3)))
S2 = tuple(permutations(range(2)))
IDQ = tuple(range(18))
IDA = tuple(range(6))


def require(ok, message, witness=None):
    if not ok:
        raise AssertionError((message, witness))


def tick():
    require(time.monotonic() - START < 30, '30-second diagnostic deadline')


def subsets(items, maximum=None):
    items = tuple(items)
    for size in range(len(items) + 1 if maximum is None else min(maximum, len(items)) + 1):
        yield from combinations(items, size)


def fine(x, y):
    if x == y:
        return 'equality',
    if x[0] != y[0]:
        return 'outside',
    return 'inside', x[1] == y[1], x[2] == y[2]


def axis_colour(x, y):
    return 'equality' if x == y else 'inside' if x[0] == y[0] else 'outside'


def compose(left, right):
    return tuple(left[right[i]] for i in range(len(right)))


def inverse(action):
    return tuple(action.index(i) for i in range(len(action)))


def pi_k(x):
    return x[0], x[1]


def pi_h(x):
    return x[0], x[2]


def relation_product(r, s):
    rows = {x: {z for y, z in s if y == x} for x in range(18)}
    return frozenset((x, z) for x, y in r for z in rows[y])


def group_models(counts):
    axis = []
    for sigma in S2:
        for local in product(S3, repeat=2):
            action = tuple(AINDEX[sigma[i], local[i][a]] for i, a in AXES)
            require(all(axis_colour(x, y) == axis_colour(AXES[action[AINDEX[x]]], AXES[action[AINDEX[y]]])
                        for x, y in product(AXES, repeat=2)), 'actual quotient fine-colour action')
            axis.append((sigma, local, action))
    require(len({a for _, _, a in axis}) == 72, 'actual quotient/owner group size')
    real, pair_lifts, quotient_lifts = [], {}, {}
    for sigma, ap, beta in axis:
        for sigma_h, bp, gamma in axis:
            if sigma_h != sigma:
                continue
            action = tuple(QINDEX[sigma[i], ap[i][a], bp[i][b]] for i, a, b in POINTS)
            require(all(fine(x, y) == fine(POINTS[action[QINDEX[x]]], POINTS[action[QINDEX[y]]])
                        for x, y in combinations(POINTS, 2)), 'actual real fine-colour action')
            require(all(pi_k(POINTS[action[j]]) == AXES[beta[AINDEX[pi_k(x)]]]
                        and pi_h(POINTS[action[j]]) == AXES[gamma[AINDEX[pi_h(x)]]]
                        for j, x in enumerate(POINTS)), 'BOTH actual quotient actions induced literally')
            real.append((action, beta, gamma))
            require((beta, gamma) not in pair_lifts, 'actual matching pair determines real action in this model')
            pair_lifts[beta, gamma] = action
            quotient_lifts.setdefault(beta, []).append(action)
    require(len(real) == 2592, 'structured real group size')
    counts['structured_actual_real_automorphisms'] = len(real)
    counts['actual_K_quotient_automorphisms'] = counts['actual_H_owner_automorphisms'] = len(axis)
    return axis, real, pair_lifts, quotient_lifts


def exact_geometry_controls(counts, witnesses, axis, real):
    k = frozenset((i, j) for i, x in enumerate(POINTS) for j, y in enumerate(POINTS) if pi_k(x) == pi_k(y))
    h = frozenset((i, j) for i, x in enumerate(POINTS) for j, y in enumerate(POINTS) if pi_h(x) == pi_h(y))
    f = frozenset((i, j) for i, x in enumerate(POINTS) for j, y in enumerate(POINTS) if x[0] == y[0])
    k_atom = frozenset((i, j) for i, j in k if i != j)
    h_atom = frozenset((i, j) for i, j in h if i != j)
    require(relation_product(k_atom, k_atom) == k, 'K is an actual RAW two-letter profile, not assumed exact')
    require(relation_product(h_atom, h_atom) == h, 'H is an actual RAW two-letter profile, not assumed exact')
    require(relation_product(k, h) == relation_product(h, k) == f, 'actual nonnested K;H=K join H')
    require(bool(k - h) and bool(h - k), 'neither K nor H contains the other')
    colours = {fine(x, y) for x, y in product(POINTS, repeat=2)}
    for colour in colours:
        atom = frozenset((i, j) for i, x in enumerate(POINTS) for j, y in enumerate(POINTS) if fine(x, y) == colour)
        require(relation_product(relation_product(k, atom), h) == relation_product(f, atom),
                'mixed exact-join K;a;H=(K join H);a on EVERY actual raw atom', colour)
        counts['actual_mixed_join_atom_identities'] += 1
    # Actual mixed-sort pair orbits, computed from the REAL group.
    for projection, induced_at in ((pi_k, 1), (pi_h, 2)):
        orbit_by_label = {}
        for x in POINTS:
            for target in AXES:
                label = 'equal_projection' if projection(x) == target else 'same_packet' if x[0] == target[0] else 'outside'
                orbit = frozenset((POINTS[a[QINDEX[x]]], AXES[rec[induced_at][AINDEX[target]]])
                                  for rec in real for a in (rec[0],))
                require(label not in orbit_by_label or orbit_by_label[label] == orbit,
                        'real/exact-quotient orbital depends ONLY on projected pair', (projection.__name__, x, target))
                orbit_by_label[label] = orbit
                counts['actual_real_quotient_orbitals'] += 1
    orbit_by_label = {}
    for q, owner in product(AXES, repeat=2):
        label = q[0] == owner[0]
        orbit = frozenset((AXES[beta[AINDEX[q]]], AXES[gamma[AINDEX[owner]]]) for _, beta, gamma in real)
        require(label not in orbit_by_label or orbit_by_label[label] == orbit,
                'K/H pair orbit determined by their COMMON coarse quotient', (q, owner))
        orbit_by_label[label] = orbit
        counts['actual_K_H_mixed_orbitals'] += 1
    witnesses['exact_nonnested_geometry'] = {'real_points': 18, 'K_fibre_size': 3, 'H_fibre_size': 3,
                                            'K_quotient_size': 6, 'H_owner_size': 6,
                                            'join_fibre_size': 9, 'raw_exact_words': ['k_atom;k_atom', 'h_atom;h_atom']}
    tick()


def preimage_controls(counts, witnesses, axis, real):
    for selected in subsets(AXES):
        if not selected:
            continue
        selected = frozenset(selected)
        full = frozenset(j for j, x in enumerate(POINTS) if pi_k(x) in selected)
        coarse = {i for i, a in selected}
        owner = {pi_h(POINTS[j]) for j in full}
        require(len(full) == 3 * len(selected), 'FULL K inverse image includes every finite fibre')
        require(owner == {(i, b) for i in coarse for b in range(3)}, 'owner image is COMPLETE inverse packet over coarse owners')
        for action, beta, _ in real:
            if {AXES[beta[AINDEX[x]]] for x in selected} == selected:
                require({action[j] for j in full} == full, 'EVERY compatible entire quotient action stabilizes full inverse image')
                counts['full_preimage_setwise_lifts'] += 1
        counts['full_K_preimages'] += 1
    # A finite F[-] coordinate identity; explicitly NOT finite-structure acl.
    closure_inputs = tuple(x for x in POINTS if x[0] == 0) + ((1, 0, 0),)
    for selected in subsets(closure_inputs):
        # Nine points in the first grid plus one in the second: exactly
        # 1,024 inputs, without enumerating the unused 2^18 universe.
        grid_ids = {x[0] for x in selected}
        closure = {x for x in POINTS if x[0] in grid_ids}
        quotient_closure = {q for q in AXES if q[0] in {pi_k(x)[0] for x in selected}}
        require(closure == {x for x in POINTS if pi_k(x) in quotient_closure},
                'combinatorial F-closure commutes with full K preimage')
        counts['finite_packet_closure_identities'] += 1
    # A proper inverse-image subset can destroy a compatible lift.
    incomplete = frozenset(QINDEX[x] for x in POINTS if x[0] == 0 and x != (0, 1, 2))
    bad_beta = next(beta for sigma, local, beta in axis if sigma == (0, 1)
                    and local[0] == (1, 0, 2) and local[1] == (0, 1, 2))
    partial = {QINDEX[0, 0, 2]: QINDEX[0, 1, 0]}
    matching = [a for a, beta, _ in real if beta == bad_beta and all(a[x] == y for x, y in partial.items())]
    require(bool(matching) and not any({a[j] for j in incomplete} == incomplete for a in matching),
            'missing ONE K-fibre point can destroy the compatible partial-map/entire-beta lift')
    witnesses['missing_full_preimage'] = {'missing_real_point': (0, 1, 2),
                                         'compatible_source_map': (((0, 0, 2), (0, 1, 0)),),
                                         'quotient_a_permutation': (1, 0, 2)}
    counts['negative_incomplete_K_preimage'] += 1
    tick()


def partial_maps(source):
    for domain in subsets(source):
        for targets in permutations(source, len(domain)):
            p = dict(zip(domain, targets))
            if all(fine(POINTS[x], POINTS[y]) == fine(POINTS[p[x]], POINTS[p[y]])
                   for x, y in product(domain, repeat=2)):
                yield p


def joint_lift_controls(counts, witnesses, axis, real, pair_lifts, quotient_lifts):
    source = tuple(QINDEX[x] for x in ((0, 0, 2), (0, 0, 0), (0, 1, 2)))
    partials = tuple(partial_maps(source))
    for p in partials:
        good_beta = {beta for _, _, beta in axis
                     if all(beta[AINDEX[pi_k(POINTS[x])]] == AINDEX[pi_k(POINTS[y])] for x, y in p.items())}
        good_gamma = {gamma for _, _, gamma in axis
                      if all(gamma[AINDEX[pi_h(POINTS[x])]] == AINDEX[pi_h(POINTS[y])] for x, y in p.items())}
        for beta in good_beta:
            require(any(all(a[x] == y for x, y in p.items()) for a in quotient_lifts[beta]),
                    'finite REAL partial map plus ENTIRE beta has an actual fine-colour lift', p)
            counts['ordinary_entire_beta_partial_lifts'] += 1
        for beta, gamma in pair_lifts:
            if beta in good_beta and gamma in good_gamma:
                a = pair_lifts[beta, gamma]
                require(all(a[x] == y for x, y in p.items()), 'compatible REAL p, ENTIRE beta and ENTIRE gamma lift jointly', p)
                counts['relative_entire_beta_gamma_lifts'] += 1
    # Empty real-domain compatibility still requires WHOLE coarse agreement.
    disagreeing = next((b, g) for sb, _, b in axis for sg, _, g in axis if sb != sg)
    require(disagreeing not in pair_lifts, 'different coarse actions cannot lift even for EMPTY p')
    z = QINDEX[0, 0, 0]
    require(pair_lifts[IDA, IDA][z] != QINDEX[0, 0, 1], 'owner mismatch cannot be hidden by compatible K projection')
    require(pair_lifts[IDA, IDA][z] != QINDEX[0, 1, 0], 'K mismatch cannot be hidden by compatible H owner')
    # Both quotient actions retain information beyond a prescribed singleton.
    extra_beta = next(b for sigma, local, b in axis if sigma == (0, 1)
                      and local[0] == (0, 1, 2) and local[1] == (1, 0, 2))
    extra_gamma = extra_beta
    require(extra_beta[AINDEX[0, 0]] == IDA[AINDEX[0, 0]] and extra_beta != IDA,
            'entire beta is strictly more than its singleton restriction')
    require(pair_lifts[extra_beta, IDA][z] == pair_lifts[IDA, IDA][z] == z
            and pair_lifts[extra_beta, IDA] != pair_lifts[IDA, IDA], 'two actual lifts retain different entire betas')
    require(pair_lifts[IDA, extra_gamma][z] == z
            and pair_lifts[IDA, extra_gamma] != pair_lifts[IDA, IDA], 'two actual lifts retain different entire owner gammas')
    witnesses['entire_action_not_singleton'] = {'source_singleton': (0, 0, 0),
                                              'changed_action_outside_source_packet': 'swap coordinate values 0,1 in grid 1'}
    counts['fine_source_partial_isomorphisms'] = len(partials)
    counts['negative_coarse_compatibility'] += 1
    counts['negative_real_owner_compatibility'] += 1
    counts['negative_real_K_compatibility'] += 1
    tick()


def owner_cover_controls(counts, witnesses, axis):
    coarse_image = {a: sigma for sigma, _, a in axis}
    kernel = tuple(a for sigma, _, a in axis if sigma == (0, 1))
    require(set(coarse_image.values()) == set(S2), 'owner cover action ONTO coarse Aut')
    require(all(any(k[AINDEX[x]] == AINDEX[y] for k in kernel)
                for x, y in product(AXES, repeat=2) if x[0] == y[0]),
            'owner-cover kernel is transitive on EVERY complete owner fibre')
    for x, y in product(AXES, repeat=2):
        for coarse in S2:
            if coarse[x[0]] != y[0]:
                continue
            initial = next(a for sigma, _, a in axis if sigma == coarse)
            image = AXES[initial[AINDEX[x]]]
            adjust = next(k for k in kernel if k[AINDEX[image]] == AINDEX[y])
            result = compose(adjust, initial)
            require(result[AINDEX[x]] == AINDEX[y] and coarse_image[result] == coarse,
                    'onto plus transitive kernel lifts a GIVEN coarse action and selected owner point')
            counts['prescribed_coarse_and_owner_point_lifts'] += 1
    # Onto but no fibre-transitive kernel: only permute grids, fix b labels.
    no_kernel = tuple(a for _, local, a in axis if local == ((0, 1, 2), (0, 1, 2)))
    require({coarse_image[a] for a in no_kernel} == set(S2)
            and not any(a[AINDEX[0, 0]] == AINDEX[0, 1] and coarse_image[a] == (0, 1) for a in no_kernel),
            'ONTO alone does not lift the selected owner point')
    # Fibre-transitive kernel but NOT onto: fix the two coarse owners.
    require(all(coarse_image[a] == (0, 1) for a in kernel), 'kernel-transitivity alone does not lift a coarse swap')
    # Incomplete owner preimage: fibre sizes 3 and 2 forbid a coarse swap.
    incomplete = frozenset(AXES) - {(1, 2)}
    preserving = tuple(a for _, _, a in axis if {AXES[a[AINDEX[x]]] for x in incomplete} == incomplete)
    require(bool(preserving) and not any(coarse_image[a] == (1, 0) for a in preserving),
            'partial owner packet can destroy surjectivity to coarse Aut')
    witnesses['owner_cover_negative_premises'] = {'onto_without_transitive_kernel': 'grid permutations, no b motion',
                                                 'transitive_kernel_without_onto': 'independent b permutations, no grid swap',
                                                 'incomplete_owner_fibres': (3, 2)}
    counts['negative_missing_owner_kernel'] += 1
    counts['negative_missing_owner_onto'] += 1
    counts['negative_incomplete_owner_cover'] += 1
    tick()


def point_conjugation_controls(counts, witnesses, axis, real):
    owner_of = {a: gamma for a, _, gamma in real}
    real_set = set(owner_of)
    target = QINDEX[0, 0, 2]
    to_source = {x: next(a for a, _, _ in real if a[x] == target) for x in range(18)}
    singleton_ext = {}
    for action, _, gamma in real:
        if action[target] == target:
            singleton_ext.setdefault(gamma, action)
    for x, y in product(range(18), repeat=2):
        gx, hy = to_source[x], to_source[y]
        og, oh = owner_of[gx], owner_of[hy]
        for _, _, prescribed in axis:
            if prescribed[AINDEX[pi_h(POINTS[x])]] != AINDEX[pi_h(POINTS[y])]:
                continue
            middle_owner = compose(oh, compose(prescribed, inverse(og)))
            require(middle_owner in singleton_ext, 'conjugated ENTIRE owner action is compatible on original singleton')
            k = singleton_ext[middle_owner]
            beta = compose(inverse(hy), compose(k, gx))
            require(beta in real_set and beta[x] == y and owner_of[beta] == prescribed,
                    'h^-1 k g sends ACTUAL point and induces EXACT prescribed owner action',
                    (POINTS[x], POINTS[y], prescribed))
            packet = {j for j, p in enumerate(POINTS) if p[0] == POINTS[x][0]}
            require({POINTS[beta[j]][0] for j in packet} == {POINTS[y][0]}, 'whole finite packet follows chosen point')
            wrong = compose(prescribed, compose(oh, inverse(og)))
            if wrong != middle_owner:
                witnesses.setdefault('noncommuting_point_conjugation', {'x': POINTS[x], 'y': POINTS[y],
                                                                      'correct_owner': middle_owner,
                                                                      'wrong_owner': wrong})
            counts['prescribed_point_conjugation_lifts'] += 1
    require('noncommuting_point_conjugation' in witnesses, 'conjugation order tested in a NONABELIAN owner action')
    tick()


def safety_and_root_controls(counts, witnesses, axis, real, pair_lifts, quotient_lifts):
    palette = {'outside'}
    raw_safe = {('outside',)}
    matrix_by_quotient_colour = {}
    for u, v in permutations(AXES, 2):
        label = axis_colour(u, v)
        matrix = {fine(x, y) for x in POINTS for y in POINTS if pi_k(x) == u and pi_k(y) == v}
        require(label not in matrix_by_quotient_colour or matrix_by_quotient_colour[label] == matrix,
                'full KxK fine support depends only on actual quotient colour')
        matrix_by_quotient_colour[label] = matrix
    quotient_safe = {q for q, matrix in matrix_by_quotient_colour.items() if matrix <= raw_safe}
    require(quotient_safe == palette, 'safe quotient palette uses EVERY fine matrix entry')
    partly_safe = raw_safe | {('inside', False, True)}
    u, v = (0, 0), (0, 1)
    representative = fine((0, 0, 0), (0, 1, 0))
    require(representative in partly_safe
            and not matrix_by_quotient_colour['inside'] <= partly_safe,
            'safe representatives do NOT make the whole quotient colour safe')
    witnesses['representative_safe_matrix_unsafe'] = {'quotient_pair': (u, v), 'safe_representative_colour': representative,
                                                     'full_matrix_colours': tuple(sorted(matrix_by_quotient_colour['inside']))}
    counts['negative_representative_only_safety'] += 1
    # Noncanonical original target b=2 must be hit LITERALLY, not only in K.
    a0 = (0, 0, 2)
    target = QINDEX[a0]
    for packet in range(2):
        points = tuple(x for x in POINTS if x[0] == packet)
        cliques = set(subsets(points, 3)) | {points}
        cliques.discard(())
        for zset in sorted(cliques, key=lambda z: (len(z), z)):
            require(all(fine(x, y) not in raw_safe for x, y in combinations(zset, 2)), 'actual original unsafe clique')
            projected = {pi_k(x) for x in zset}
            require(all(axis_colour(x, y) not in quotient_safe for x, y in combinations(projected, 2)),
                    'unsafe clique projects to unsafe DISTINCT K classes, singleton projection allowed')
            counts['singleton_unsafe_quotient_projections'] += int(len(projected) == 1)
            for z in zset:
                iz, qz, hz = QINDEX[z], AINDEX[pi_k(z)], AINDEX[pi_h(z)]
                for sigma, _, beta in axis:
                    if beta[qz] != AINDEX[pi_k(a0)]:
                        continue
                    ordinary = next(a for a in quotient_lifts[beta] if a[iz] == target)
                    require(all(POINTS[ordinary[QINDEX[x]]][0] == 0 for x in zset),
                            'ordinary full-preimage lift transports ENTIRE clique into original F closure')
                    counts['ordinary_literal_root_lifts'] += 1
                    for sigma_h, _, gamma in axis:
                        if sigma_h != sigma or gamma[hz] != AINDEX[pi_h(a0)]:
                            continue
                        lifted = pair_lifts[beta, gamma]
                        require(lifted[iz] == target
                                and all(POINTS[lifted[QINDEX[x]]][0] == 0 for x in zset),
                                'relative root lift preserves BOTH ENTIRE actions and hits selected actual a')
                        counts['relative_literal_root_lifts'] += 1
                        counts['noncanonical_b_root_targets'] += int(z[2] != a0[2])
                counts['selected_unsafe_clique_roots'] += 1
    witnesses['literal_original_root'] = {'original_target': a0, 'target_b_is_noncanonical': True}
    tick()


def check():
    global START
    START = time.monotonic()
    signal.signal(signal.SIGALRM, lambda *_: (_ for _ in ()).throw(TimeoutError('30-second diagnostic limit')))
    signal.alarm(30)
    counts, witnesses = Counter(), {}
    axis, real, pair_lifts, quotient_lifts = group_models(counts)
    exact_geometry_controls(counts, witnesses, axis, real)
    preimage_controls(counts, witnesses, axis, real)
    joint_lift_controls(counts, witnesses, axis, real, pair_lifts, quotient_lifts)
    owner_cover_controls(counts, witnesses, axis)
    point_conjugation_controls(counts, witnesses, axis, real)
    safety_and_root_controls(counts, witnesses, axis, real, pair_lifts, quotient_lifts)
    signal.alarm(0)
    return {'status': 'PASS', 'scope': 'bounded B029 genuine finite exact-grid and group-lifting diagnostics',
            'counts': dict(sorted(counts.items())), 'witnesses': witnesses,
            'seconds': round(time.monotonic() - START, 3),
            'limits': 'No infinite acl/source/CCO/closed-SAP/EPPA, ambient joint-lifting theorem or coherent section certification.'}


if __name__ == '__main__':
    print(json.dumps(check(), sort_keys=True))
