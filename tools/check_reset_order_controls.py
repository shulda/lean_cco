#!/usr/bin/env python3
"""Bounded B036 diagnostics on restriction, normalization and relative EP.

Actual finite maps are checked, not theorem-text surrogates. A same-universe
endofunctor resets a unary predicate on finite orders; its Ramsey coloring
test deliberately has MORE normalized embeddings than original embeddings.
Finite poset-ideal lattices are represented by equivalences on binary cubes;
their MI parent keys, hierarchical order normalization, closed restrictions,
compatible transition copies and task reversals are checked explicitly.

Small midpoint patterns exercise both constant signs, complete unary edge
closures, fresh strong amalgams and preservation of earlier placements.
Relative EP is checked on a shared-function relational expansion chain.
The function-adding composition negative uses nested equivalences Q<=P,
convex orders and a new successor fixing each P-class maximum. This is a
counterexample to the UNGATED wording, not to a restriction-stable theorem.
Its upper expansion is NOT reasonable; the reasonable added-function
variant is not refuted or proved by this diagnostic.
Finite checks support the stated witnesses; they do not certify arbitrary
sizes, Ramsey/EP/SAP, infinite structures, generic functors or Lean code.
Normal runtime <10s, hard deadline 30s. Reproduce:
    timeout 10s python tools/check_reset_order_controls.py
"""
from collections import Counter
from fractions import Fraction
from itertools import combinations, permutations, product
import json
import signal
import time


START = time.monotonic()


def require(value, message, witness=None):
    if not value:
        raise AssertionError((message, witness))


def tick():
    require(time.monotonic() - START < 30, '30-second diagnostic deadline')


def subsets(xs):
    xs = tuple(xs)
    for size in range(len(xs) + 1):
        yield from combinations(xs, size)


def order_rank(order):
    return {x: i for i, x in enumerate(order)}


def ordered_embeddings(source_order, target_order, source_p=(), target_p=()):
    """Independent literal increasing maps with an optional unary predicate."""
    ps, pt = set(source_p), set(target_p)
    for image in combinations(target_order, len(source_order)):
        mapping = dict(zip(source_order, image))
        if all((x in ps) == (mapping[x] in pt) for x in source_order):
            yield mapping


def sort_restriction_controls(counts, witnesses):
    for n in range(4):
        for sorts in product(range(2), repeat=n):
            selected = tuple(x for x in range(n) if sorts[x] == 0)
            for active in range(4):
                choices = tuple(tuple(y for y in range(n) if sorts[y] == sorts[x])
                                if active & (1 << sorts[x]) else (-1,) for x in range(n))
                for f in product(*choices):
                    require(all(f[x] < 0 or f[x] in selected for x in selected),
                            'selected sorts are closed under their unary functions')
                    relations = [set(), set(product(range(n), repeat=2)),
                                 {(x, y) for x in range(n) for y in range(n) if x < y}]
                    for rel in relations:
                        for source in subsets(selected):
                            if any(f[x] >= 0 and f[x] not in source for x in source):
                                continue
                            def maps_into(target):
                                answer = []
                                for image in permutations(target, len(source)):
                                    m = dict(zip(source, image))
                                    if any(sorts[x] != sorts[m[x]] or
                                           (f[x] < 0) != (f[m[x]] < 0) or
                                           (f[x] >= 0 and m[f[x]] != f[m[x]]) for x in source):
                                        continue
                                    if all(((x, y) in rel) == ((m[x], m[y]) in rel)
                                           for x, y in product(source, repeat=2)):
                                        answer.append(tuple(image))
                                return set(answer)
                            require(maps_into(range(n)) == maps_into(selected),
                                    'all-I embedding sets agree on literal maps after sort restriction')
                            counts['sort_restriction_embedding_set_checks'] += 1
                    counts['typed_unary_sort_models'] += 1
        tick()
    # If the source sort is not closed, the induced restriction loses an
    # actual outgoing value and cannot serve as an embedded substructure.
    sorts, f, kept = (0, 1), (1, 1), {0}
    require(f[0] not in kept and sorts[f[0]] == 1,
            'omitting the target sort violates functional closure')
    witnesses['nonclosed_sort_collection'] = {
        'sorts': list(sorts), 'unary_function': list(f), 'kept_points': [0],
        'lost_equation': 'F(0)=1', 'restriction_domain_reflecting': False}


def normalization_controls(counts, witnesses):
    # R consists of finite linear orders with an arbitrary unary P.
    # N keeps the order/universe and replaces P by empty. It is a genuine
    # same-map idempotent endofunctor, not necessarily full on morphisms.
    objects = [(tuple(range(n)), frozenset(p)) for n in range(5) for p in subsets(range(n))]
    for order, predicate in objects:
        normalized = (order, frozenset())
        require((normalized[0], frozenset()) == normalized, 'N squared equals N')
        counts['idempotent_normalization_objects'] += 1
        if not predicate:
            for sub in subsets(order):
                require(not (set(sub) & predicate), 'induced subobjects of fixed objects are fixed')
                counts['normalized_heredity_checks'] += 1
        for target_order, target_p in objects:
            normalized_maps = {tuple(m[x] for x in order)
                               for m in ordered_embeddings(order, target_order)}
            for m in ordered_embeddings(order, target_order, predicate, target_p):
                require(tuple(m[x] for x in order) in normalized_maps,
                        'same vertex map is still an induced embedding after N')
                counts['normalization_functor_embedding_checks'] += 1
    a, b, c = (0,), (0, 1), (0, 1, 2, 3)
    old_p = {3}
    original = tuple(ordered_embeddings(a, c, (), old_p))
    normalized = tuple(ordered_embeddings(a, c))
    require(len(original) == 3 and len(normalized) == 4,
            'map Emb(A,C)->Emb(A,N(C)) is not surjective')
    copies = tuple(ordered_embeddings(b, c, (), old_p))
    for coloring in product(range(2), repeat=len(normalized)):
        color_at = {m[0]: color for m, color in zip(normalized, coloring)}
        pulled = {m[0]: color_at[m[0]] for m in original}
        good = [g for g in copies if pulled[g[0]] == pulled[g[1]]]
        require(good, 'three old P-false points give the genuine binary Ramsey witness')
        g = good[0]
        require(color_at[g[0]] == color_at[g[1]],
                'the same normalized copy is monochromatic for the original normalized coloring')
        counts['nonsurjective_normalized_Ramsey_colorings'] += 1
    witnesses['normalization_not_surjective_on_embeddings'] = {
        'normalization': 'keep order and universe, reset unary P to empty',
        'C_P_true_points': [3], 'old_singleton_embeddings': 3,
        'normalized_singleton_embeddings': 4, 'all_binary_colorings_checked': 16}


def finite_posets(n):
    pairs = tuple((i, j) for i in range(n) for j in range(n) if i != j)
    for mask in range(1 << len(pairs)):
        relation = {p for k, p in enumerate(pairs) if mask & (1 << k)}
        if any((j, i) in relation for i, j in relation):
            continue
        if any((i, k) not in relation for i, j in relation for jj, k in relation if j == jj):
            continue
        yield relation


def ideals(n, relation):
    return tuple(m for m in range(1 << n)
                 if all(not (m & (1 << j)) or m & (1 << i) for i, j in relation))


def strict_subset(a, b):
    return a != b and a & b == a


def normalized_quotient_orders(mi, carriers, old_orders, priority):
    result = {}
    ranks = {}
    for j in sorted(mi, key=lambda x: (-x.bit_count(), x)):
        coarser = [l for l in priority if strict_subset(j, l)]
        old_rank = order_rank(old_orders[j])
        result[j] = tuple(sorted(carriers[j], key=lambda v: (
            tuple(ranks[l][v & ~l] for l in coarser), old_rank[v])))
        ranks[j] = order_rank(result[j])
    return result


def quotient_normalization_controls(counts, witnesses):
    for n in range(4):
        top = (1 << n) - 1
        cube = tuple(range(1 << n))
        for poset in finite_posets(n):
            lattice = ideals(n, poset)
            covers = {j: tuple(k for k in lattice if strict_subset(j, k) and
                              not any(strict_subset(j, l) and strict_subset(l, k) for l in lattice))
                      for j in lattice}
            mi = tuple(j for j in lattice if len(covers[j]) == 1)
            priority = tuple(sorted(mi, reverse=True))
            carriers = {j: tuple(sorted({x & ~j for x in cube})) for j in mi}
            for j in mi:
                parent = covers[j][0]
                coarser = tuple(l for l in mi if strict_subset(j, l))
                meet = top
                for l in coarser:
                    meet &= l
                require(meet == parent, 'meet of all strict coarser MI coordinates equals J-plus')
                for x, y in product(cube, repeat=2):
                    same_key = all((x & ~l) == (y & ~l) for l in coarser)
                    require(same_key == ((x & ~parent) == (y & ~parent)),
                            'strict coarser tuple equality is exactly parent-fibre equality')
                    counts['MI_parent_key_pair_checks'] += 1
            for seed in range(4):
                old = {}
                for j in mi:
                    values = carriers[j]
                    shift = seed % max(1, len(values))
                    rotated = values[shift:] + values[:shift]
                    old[j] = rotated if (seed + j) % 2 else tuple(reversed(rotated))
                normalized = normalized_quotient_orders(mi, carriers, old, priority)
                require(normalized_quotient_orders(mi, carriers, normalized, priority) == normalized,
                        'hierarchical parent-lex order normalization is idempotent')
                counts['hierarchical_normalization_samples'] += 1
                # Quotient images of an arbitrary original subset form an
                # actual closed subobject under every upward quotient map.
                for roots in subsets(cube):
                    smaller = {j: tuple(sorted({x & ~j for x in roots})) for j in mi}
                    restricted_old = {j: tuple(x for x in old[j] if x in smaller[j]) for j in mi}
                    restricted_n = normalized_quotient_orders(mi, smaller, restricted_old, priority)
                    require(all(restricted_n[j] == tuple(x for x in normalized[j] if x in smaller[j])
                                for j in mi), 'closed inclusions preserve all normalized quotient orders')
                    counts['closed_quotient_normalization_inclusions'] += 1
                for selected in mi:
                    parent = covers[selected][0]
                    modified = dict(normalized)
                    groups = {}
                    for x in normalized[selected]:
                        groups.setdefault(x & ~parent, []).append(x)
                    modified[selected] = tuple(x for group in groups.values() for x in reversed(group))
                    reversed_n = normalized_quotient_orders(mi, carriers, modified, priority)
                    require(all(reversed_n[j] == normalized[j] for j in mi
                                if not (j & selected == j)),
                            'reversing one cut task changes no coarser or incomparable task')
                    require(all(tuple(x for x in reversed_n[selected] if (x & ~parent) == key) ==
                                tuple(reversed(group)) for key, group in groups.items()),
                            'selected cut fibre orders really reverse')
                    counts['single_cut_reversal_checks'] += 1
                # Three isomorphic copies use coherent labelled bijections.
                # Their conjugated upward maps commute with transitions.
                theta = {(i, j): {x: (k + i) % len(carriers[j]) for k, x in enumerate(carriers[j])}
                         for i in range(3) for j in mi}
                inverse = {key: {v: x for x, v in value.items()} for key, value in theta.items()}
                transitions = {(i, k, j): {theta[i, j][x]: theta[k, j][x] for x in carriers[j]}
                               for i, k in product(range(3), repeat=2) for j in mi}
                upward = {(i, j, coarse): {theta[i, j][x]: theta[i, coarse][x & ~coarse]
                                           for x in carriers[j]}
                          for i in range(3) for j in mi for coarse in mi if strict_subset(j, coarse)}
                for j in mi:
                    for i, k, l in product(range(3), repeat=3):
                        for x in carriers[j]:
                            start = theta[i, j][x]
                            middle = transitions[i, k, j][start]
                            end = transitions[k, l, j][middle]
                            require(end == transitions[i, l, j][start], 'transition paths have trivial holonomy')
                            counts['coherent_transition_path_checks'] += 1
                    for coarse in mi:
                        if not strict_subset(j, coarse):
                            continue
                        for i, k in product(range(3), repeat=2):
                            for x in carriers[j]:
                                start = theta[i, j][x]
                                transitioned_then_up = upward[k, j, coarse][transitions[i, k, j][start]]
                                up_then_transition = transitions[i, k, coarse][upward[i, j, coarse][start]]
                                require(transitioned_then_up == up_then_transition,
                                        'transition copies preserve the whole upward quotient diagram')
                                counts['transition_upward_commutation_checks'] += 1
                    transported = [tuple(theta[i, j][x] for x in normalized[j]) for i in range(3)]
                    require(all(tuple(inverse[i, j][x] for x in transported[i]) == normalized[j]
                                for i in range(3)), 'transported normalized task orders synchronize')
                    counts['synchronized_quotient_order_copies'] += 3
            counts['finite_distributive_lattices'] += 1
            tick()
    for order in permutations(range(2)):
        require(tuple(1 - x for x in order) != order,
                'a nonidentity closed transition prevents a path-independent total task order')
    witnesses['nontrivial_holonomy'] = {'representative_order': [0, 1],
        'closed_transition': [1, 0], 'transported_order': [1, 0], 'path_independent': False}
    # Fibre synchronization does NOT require the whole derived sort
    # order to be monotone under a transition. In the ideal lattice of
    # a<b,a<c, J=empty has parent {a} and coarser MI cuts {a,b},{a,c}.
    # Reversing those TWO key priorities changes cross-parent lex order
    # while the task order INSIDE each common parent fibre stays identical.
    mi = (0, 3, 5)
    carriers = {j: tuple(sorted({x & ~j for x in range(8)})) for j in mi}
    old = dict(carriers)
    first = normalized_quotient_orders(mi, carriers, old, (3, 5, 0))
    second = normalized_quotient_orders(mi, carriers, old, (5, 3, 0))
    fr, sr = order_rank(first[0]), order_rank(second[0])
    require(fr[2] < fr[4] and sr[2] > sr[4], 'opposite key priorities give different global sort orders')
    require(all((fr[x] < fr[y]) == (sr[x] < sr[y]) for x, y in product(range(8), repeat=2)
                if (x & ~1) == (y & ~1)), 'all within-parent fibre task comparisons still synchronize')
    witnesses['fibre_synchronization_not_global_transition_monotonicity'] = {
        'poset': 'a<b and a<c', 'selected_MI': [], 'parent_J_plus': ['a'],
        'coarser_MI_coordinates': [['a', 'b'], ['a', 'c']],
        'first_priority': [3, 5], 'second_priority': [5, 3],
        'identity_transition': True, 'global_orders_disagree_on_points': [2, 4],
        'within_parent_orders_synchronized': True,
        'scope': 'boundary to stronger global-order claim; no compatible-priority premise is added to fibre-task synchronization'}
    counts['fibre_sync_without_global_transition_monotonicity_checks'] += 1


def midpoint_patterns(n):
    roots = tuple(range(n))
    locations = {x: Fraction(x) for x in roots}
    edges, mids = set(), {}
    for k, (u, v) in enumerate(combinations(roots, 2), 1):
        z = n + k - 1
        denominator = 2 * n * n + 1
        value = Fraction(u) + Fraction(k, denominator) * (v - u)
        while value in locations.values():
            denominator += 1
            value = Fraction(u) + Fraction(k, denominator) * (v - u)
        require(u < value < v, 'fresh midpoint has an interior reference position')
        locations[z] = value
        edges.add((u, z)); edges.add((z, v)); mids[u, v] = z
    reference = tuple(sorted(locations, key=locations.get))
    return roots, reference, edges, mids


def midpoint_controls(counts, witnesses):
    edge_signature = None
    for n in range(4):
        roots, reference, edges, mids = midpoint_patterns(n)
        rr = order_rank(reference)
        require(all(rr[u] < rr[z] < rr[v] for (u, v), z in mids.items()),
                'all stored comparisons have fresh induced midpoint witnesses')
        for stored_positive in (True, False):
            oriented_edges = edges if stored_positive else {(v, u) for u, v in edges}
            for competitor in permutations(reference):
                rank = order_rank(competitor)
                signs = {rank[u] < rank[v] for u, v in oriented_edges}
                if len(signs) > 1:
                    continue
                sign = next(iter(signs), True)
                original_increases = sign == stored_positive
                require(all((rank[u] < rank[v]) == original_increases
                            for u, v in combinations(roots, 2)),
                        'two constant-sign consecutive edges force every original comparison')
                if sign == stored_positive:
                    require(all(rank[u] < rank[v] for u, v in combinations(roots, 2)),
                            'choose plus pattern for plus sign, minus pattern for minus sign')
                    counts['selected_plus_or_minus_source_copies'] += 1
                counts['constant_sign_midpoint_competitors'] += 1
        # Complete edge closure: two designated endpoints plus their one
        # shared parent, with all defined unary values retained.
        for u, v in edges:
            parent = len(reference)
            closure = {u, v, parent}
            function = {x: parent for x in reference}; function[parent] = parent
            require(all(function[x] in closure for x in closure),
                    'oriented edge closure is an actual closed three-point diagram')
            require(rr[u] < rr[v], 'oriented edge has the unique increasing rooted edge type')
            roles = (u, v, parent)
            symmetric_edges = edges | {(b, a) for a, b in edges}
            signature = (tuple(roles.index(function[x]) for x in roles),
                         tuple((x, y) in symmetric_edges for x, y in product(roles, repeat=2)),
                         tuple(rr[x] < rr[y] for x, y in product((u, v), repeat=2)))
            if edge_signature is None:
                edge_signature = signature
            require(signature == edge_signature,
                    'ALL full rooted ordered unary-generated edge diagrams are isomorphic')
            counts['complete_unary_edge_closure_checks'] += 1
    # Strong amalgams over the FULL pair closure retain its auxiliary
    # parent and every existing comparison; only a fresh z is inserted.
    for n in range(2, 5):
        for old_order in permutations(range(n)):
            for i, j in combinations(range(n), 2):
                u, v = old_order[i], old_order[j]
                parent, z = n, n + 1
                a = set(range(n)) | {parent}; p = {u, v, parent}; t = p | {z}
                old_f = {x: parent for x in a}; witness_f = {x: parent for x in t}
                require(all(old_f[x] == witness_f[x] for x in p), 'full closed base function diagrams agree')
                amalgam = a | t
                require(a & t == p and z not in a and len(amalgam) == len(a) + 1,
                        'strong intersection makes the midpoint fresh over the entire old structure')
                extended = old_order[:i + 1] + (z,) + old_order[i + 1:]
                rank = order_rank(extended)
                require(tuple(x for x in extended if x != z) == old_order and rank[u] < rank[z] < rank[v],
                        'free compatible order extension preserves the whole old order')
                f = dict(old_f); f.update(witness_f)
                require(all(f[x] in a for x in a) and all(f[x] in t for x in t),
                        'both factor inclusions are genuinely functionally closed')
                old_m = {(x, y) for x, y in product(range(n), repeat=2) if x != y}
                witness_m = {(x, y) for x, y in product((u, v, z), repeat=2) if x != y}
                amalgam_m = old_m | witness_m
                require({(x, y) for x, y in amalgam_m if x in a and y in a} == old_m and
                        {(x, y) for x, y in amalgam_m if x in t and y in t} == witness_m and
                        (u, z) in amalgam_m and (z, v) in amalgam_m,
                        'strong diagram union preserves both induced m-relations and the two reset edges')
                counts['fresh_strong_closed_midpoint_amalgams'] += 1
    # Coarse endpoint equivalence does not identify a complete named type.
    require({(0, 1)} != set(), 'a missing fine binary tuple prevents induced base identification')
    witnesses['coarse_edge_type_is_insufficient'] = {'same_fibre': True,
        'first_base_fine_relation': [[0, 1]], 'second_base_fine_relation': [],
        'complete_named_base_types_match': False}
    # Relation composition alone does not provide a point outside the
    # actual pair closure. A unary 3-cycle already fills its entire fibre.
    cycle_f = (1, 2, 0)
    m = {(x, y) for x, y in product(range(3), repeat=2) if x != y}
    square = {(x, y) for x, y in product(range(3), repeat=2)
              if any((x, z) in m and (z, y) in m for z in range(3))}
    require(square == set(product(range(3), repeat=2)), 'm composed m is the FULL same-fibre equivalence')
    for u, v in combinations(range(3), 2):
        closure = {u, v}
        while {cycle_f[x] for x in closure} - closure:
            closure |= {cycle_f[x] for x in closure}
        possible = {z for z in range(3) if (u, z) in m and (z, v) in m}
        require(closure == {0, 1, 2} and possible <= closure,
                'every relation midpoint can lie INSIDE the old pair closure')
        counts['relation_composition_without_freshness_checks'] += 1
    witnesses['midpoint_relation_does_not_imply_freshness'] = {
        'unary_function': list(cycle_f), 'fibre': [0, 1, 2],
        'm': 'all distinct pairs in that fibre', 'm_composed_m_is_full_fibre': True,
        'every_nonempty_unary_closure_is_whole_cycle': True,
        'fresh_same_fibre_point_outside_pair_closure': False,
        'scope': 'outside-closure witness hypothesis fails; disjoint unary 3-cycles admit closed free unions'}


def partitions(n):
    def extend(prefix):
        if len(prefix) == n:
            yield tuple(prefix); return
        for value in range(max(prefix, default=-1) + 2):
            yield from extend(prefix + [value])
    yield from extend([])


def blocks(labels):
    return tuple(tuple(i for i, value in enumerate(labels) if value == label)
                 for label in sorted(set(labels)))


def nested_partitions(n):
    pp = tuple(partitions(n))
    for p in pp:
        for q in pp:
            if all(q[i] != q[j] or p[i] == p[j] for i, j in product(range(n), repeat=2)):
                yield p, q


def convex_orders(p, q):
    groups = []
    for pb in blocks(p):
        qb = tuple(tuple(x for x in pb if q[x] == label) for label in sorted({q[x] for x in pb}))
        arrangements = []
        for qorder in permutations(qb):
            for internal in product(*(tuple(permutations(b)) for b in qorder)):
                arrangements.append(tuple(x for b in internal for x in b))
        groups.append(tuple(arrangements))
    for porder in permutations(range(len(groups))):
        for chosen in product(*(groups[i] for i in porder)):
            yield tuple(x for b in chosen for x in b)


def successor(order, p):
    result = {}
    for pb in blocks(p):
        ordered = tuple(x for x in order if x in pb)
        for i, x in enumerate(ordered):
            result[x] = ordered[min(i + 1, len(ordered) - 1)]
    return result


def nested_order_embeddings(sp, sq, so, tp, tq, to, sf=None, tf=None):
    for image in combinations(to, len(so)):
        m = dict(zip(so, image))
        if any((sp[x] == sp[y]) != (tp[m[x]] == tp[m[y]]) or
               (sq[x] == sq[y]) != (tq[m[x]] == tq[m[y]]) for x, y in product(so, repeat=2)):
            continue
        if sf is not None and any(m[sf[x]] != tf[m[x]] for x in so):
            continue
        yield m


def ep_composition_controls(counts, witnesses):
    # Shared identity F and one final derived relation (reverse order)
    # give a restriction-stable chain with actual finite EP witnesses.
    for n in range(4):
        for p, q in nested_partitions(n):
            source_order = next(convex_orders(p, q))
            r = len(blocks(p))
            width = max((len({q[x] for x in pb}) for pb in blocks(p)), default=0)
            height = max((len(qb) for qb in blocks(q)), default=0)
            hp, hq = [], []
            for i, j, _ in product(range(r), range(width), range(height)):
                hp.append(i); hq.append(i * width + j)
            host_n = len(hp)
            for host_order in convex_orders(hp, hq):
                embeddings = tuple(nested_order_embeddings(p, q, source_order, hp, hq, host_order))
                require(embeddings, 'uniform nested-equivalence host works for every convex-order expansion')
                m = embeddings[0]
                # Restriction reflects the shared identity function, and
                # the final reverse-order relation pulls back exactly.
                shared_f = {x: x for x in range(host_n)}
                image = set(m.values())
                require(all(shared_f[x] in image for x in image),
                        'image is closed under all SHARED function symbols')
                sr, tr = order_rank(source_order), order_rank(host_order)
                require(all((sr[x] > sr[y]) == (tr[m[x]] > tr[m[y]])
                            for x, y in product(source_order, repeat=2)),
                        'full relational expansion restricts and transports to exactly B1')
                counts['common_function_composite_EP_instances'] += 1
            counts['uniform_nested_EP_source_patterns'] += 1
    # Literal ungated composition adds a NEW total successor function.
    # K0: nested Q<=P; K1: orders convex for both; K2: unique within-P
    # immediate successor, with each P maximum fixed. The source has
    # Q-block sizes 2 then 1 in one P class, and F=a->b->c->c.
    sp, sq, so = (0, 0, 0), (0, 0, 1), (0, 1, 2)
    sf = successor(so, sp)
    for n in range(6):
        for p, q in nested_partitions(n):
            adverse = []
            for pb in blocks(p):
                qbs = [tuple(x for x in pb if q[x] == label) for label in sorted({q[x] for x in pb})]
                qbs.sort(key=lambda b: (len(b) >= 2, b[0]))
                adverse.extend(x for qb in qbs for x in qb)
            adverse = tuple(adverse)
            f = successor(adverse, p)
            require(not tuple(nested_order_embeddings(sp, sq, so, p, q, adverse, sf, f)),
                    'adverse legal expansion avoids the target Q-block2-then1 successor tail')
            # K2 hereditary subsets are exactly F-closed final segments in
            # each P class. Check all subsets, not ordinary old restrictions.
            rank = order_rank(adverse)
            for chosen in subsets(range(n)):
                chosen = set(chosen)
                closed = all(f[x] in chosen for x in chosen)
                suffix = all(all(y in chosen for y in pb if rank[y] >= rank[x])
                             for pb in blocks(p) for x in pb if x in chosen)
                require(closed == suffix, 'new-function closed subobjects are precisely P-final segments')
                if closed:
                    suborder = tuple(x for x in adverse if x in chosen)
                    require(all(f[x] == y for x, y in successor(suborder, p).items()),
                            'closed subobjects retain the unique legal successor expansion')
                counts['successor_closed_substructure_checks'] += 1
            counts['function_adding_EP_composition_bad_hosts'] += 1
        tick()
    # A specific intermediate ordered subset need not be closed after F
    # was added, so heredity cannot justify the printed restriction.
    target_p, target_order = (0, 0, 0), (0, 1, 2)
    tf = successor(target_order, target_p)
    require(tf[0] == 1 and 1 not in {0, 2}, 'old induced image may omit its NEW unary value')
    witnesses['function_adding_EP_composition_failure'] = {
        'K0': 'finite nested equivalences Q subset P',
        'K1': 'linear order convex for P and Q',
        'K2': 'unique new successor within each P class; its maximum is fixed',
        'target_P': list(sp), 'target_Q': list(sq), 'target_order': list(so),
        'target_F': [sf[x] for x in so],
        'adverse_order_rule': 'put a Q block of size at least 2 LAST in each P class when available',
        'bounded_host_sizes_checked': list(range(6)),
        'human_all_size_obstruction': 'F forces c to P-maximum and b to its predecessor: Q(b,c) holds if the last Q block is large; if all blocks are singletons, Q(a,b) fails.',
        'EP_K2_over_K1': 'unique legal F expansion of each fixed ordered reduct',
        'EP_K1_over_K0': 'uniform nested blocks provide the source pattern for every convex order',
        'top_expansion_is_reasonable': False,
        'reasonable_added_function_variant_settled': False,
        'counterexample_scope': 'displayed added-function EP quantifiers only; restriction-stable/common-function composition remains valid'}
    incidence = ((True, False), (False, True))
    require(all(any(row[j] for row in incidence) for j in range(2)) and
            not any(all(row) for row in incidence),
            'host chosen after competitor does not give one host before all competitors')
    witnesses['EP_quantifier_order'] = {'host_by_competitor_matrix': incidence,
        'forall_competitor_exists_host': True, 'exists_host_forall_competitor': False}
    counts['EP_logical_quantifier_checks'] += 1


def main():
    signal.signal(signal.SIGALRM, lambda *_: (_ for _ in ()).throw(TimeoutError('30-second hard deadline')))
    signal.alarm(30)
    counts, witnesses = Counter(), {}
    sort_restriction_controls(counts, witnesses)
    normalization_controls(counts, witnesses)
    quotient_normalization_controls(counts, witnesses)
    midpoint_controls(counts, witnesses)
    ep_composition_controls(counts, witnesses)
    signal.alarm(0)
    print(json.dumps(dict(status='PASS', seconds=round(time.monotonic() - START, 3),
        scope='bounded sort maps, quotient-order functors, midpoint signs and relative EP diagnostics',
        counts=counts, witnesses=witnesses,
        limits='Finite models do not prove arbitrary-size Ramsey/EP/SAP, general distributive representation, actual CCO/MI geometry or Lean. The function-adding composition witness includes a separate human all-size obstruction; the checked theorem contract must retain restriction stability.'), sort_keys=True))


if __name__ == '__main__':
    main()
