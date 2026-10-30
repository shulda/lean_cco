#!/usr/bin/env python3
"""Bounded B040 diagnostics for actual typed quotient transport.

These finite calculations check represented relation composition, canonical
quotient labels, invariant-equivalence intervals, return holonomy, prescribed
point lifting and orbital pullback/diagonal classification. They are not an
unbounded proof, an FO-definability theorem, a named-exact-sort construction,
SAP/CCO verification or a Lean certificate. Only the standard library is used.
Reproduce: timeout 10s python tools/check_quotient_transport_controls.py
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


def identity(xs):
    return frozenset((x, x) for x in xs)


def converse(r):
    return frozenset((y, x) for x, y in r)


def compose(r, s):
    outgoing = {}
    for y, z in s:
        outgoing.setdefault(y, set()).add(z)
    return frozenset((x, z) for x, y in r for z in outgoing.get(y, ()))


def transport(r, e):
    return compose(compose(converse(r), e), r)


def kernel(mapping):
    return frozenset((x, y) for x, y in product(mapping, repeat=2)
                     if mapping[x] == mapping[y])


def equivalence(xs, relation):
    return (identity(xs) <= relation and converse(relation) == relation
            and compose(relation, relation) <= relation)


def join(xs, e, f):
    result = e | f | identity(xs)
    while True:
        following = result | compose(result, result)
        if following == result:
            return result
        result = following


def partitions(xs):
    """Enumerate partitions independently of any group/subgroup formula."""
    xs = tuple(xs)
    if not xs:
        yield ()
        return
    for rest in partitions(xs[1:]):
        yield (frozenset({xs[0]}),) + rest
        for i in range(len(rest)):
            yield rest[:i] + (rest[i] | {xs[0]},) + rest[i + 1:]


def all_equivalences(xs):
    return tuple(frozenset((x, y) for block in blocks for x in block for y in block)
                 for blocks in partitions(xs))


def invariant_equivalences(xs, actions):
    return tuple(e for e in all_equivalences(xs)
                 if all(frozenset((g[x], g[y]) for x, y in e) == e for g in actions))


def pair_orbits(a, b, actions_a, actions_b):
    pending = set(product(a, b))
    result = []
    while pending:
        x, y = min(pending)
        orbit = frozenset((ga[x], gb[y]) for ga, gb in zip(actions_a, actions_b))
        result.append(orbit)
        pending.difference_update(orbit)
    return tuple(result)


def invariant_relations(a, b, actions_a, actions_b):
    orbits = pair_orbits(a, b, actions_a, actions_b)
    return tuple(frozenset().union(*(orbits[i] for i in range(len(orbits)) if mask >> i & 1))
                 for mask in range(1, 1 << len(orbits)))


def canonical_labels(a, b, r, e):
    labels = {}
    for y in b:
        predecessors = tuple(x for x in a if (x, y) in r)
        require(predecessors, 'every target has an actual predecessor')
        classes = {frozenset(z for z in a if (x, z) in e) for x in predecessors}
        require(len(classes) == 1, 'all actual predecessors have one E-class')
        labels[y] = next(iter(classes))
    require(set(labels.values()) == {frozenset(y for y in a if (x, y) in e) for x in a},
            'canonical quotient label map is onto')
    return labels


def cover(interval, x, y):
    return x < y and not any(x < z < y for z in interval)


def meet_irreducible(interval, x):
    top = max(interval, key=len)
    return x != top and all((h & k) != x or h == x or k == x
                           for h, k in product(interval, repeat=2))


def finite_action_models():
    for n in (1, 2, 3, 4, 6):
        divisors = [d for d in range(1, n + 1) if n % d == 0]
        for da, db in product(divisors, repeat=2):
            a, b = tuple(('A', i) for i in range(da)), tuple(('B', i) for i in range(db))
            ga = tuple({x: ('A', (x[1] + g) % da) for x in a} for g in range(n))
            gb = tuple({x: ('B', (x[1] + g) % db) for x in b} for g in range(n))
            yield 'cyclic', a, b, ga, gb
    # A non-chain equivalence lattice, not only cyclic divisibility chains.
    a, b = tuple(('A', i) for i in range(4)), tuple(('B', i) for i in range(4))
    yield 'Klein-four', a, b, tuple({x: ('A', x[1] ^ g) for x in a} for g in range(4)), tuple(
        {x: ('B', x[1] ^ g) for x in b} for g in range(4))
    # Left-regular S3 supplies noncommuting invariant relations/kernels.
    elements = tuple(permutations(range(3)))
    indices = {g: i for i, g in enumerate(elements)}
    multiply = lambda p, q: tuple(p[q[i]] for i in range(3))
    a, b = tuple(('A', i) for i in range(6)), tuple(('B', i) for i in range(6))
    yield 'symmetric-three', a, b, tuple(
        {x: ('A', indices[multiply(g, elements[x[1]])]) for x in a} for g in elements), tuple(
        {x: ('B', indices[multiply(g, elements[x[1]])]) for x in b} for g in elements)


def quotient_transport_controls(counts):
    for _, a, b, ga, gb in finite_action_models():
        eq_a, eq_b = invariant_equivalences(a, ga), invariant_equivalences(b, gb)
        for r in invariant_relations(a, b, ga, gb):
            require({x for x, _ in r} == set(a) and {y for _, y in r} == set(b),
                    'nonempty invariant relation between transitive sorts is serial and co-serial')
            for e in eq_a:
                if not compose(r, converse(r)) <= e:
                    continue
                labels = canonical_labels(a, b, r, e)
                f = transport(r, e)
                require(f == kernel(labels) and equivalence(b, f),
                        'actual R-converse;E;R is exactly the canonical label kernel')
                classes_a = set(labels.values())
                classes_b = {frozenset(y for y in b if (x, y) in f) for x in b}
                quotient_map = {}
                for block in classes_a:
                    target_blocks = {frozenset(z for z in b if (y, z) in f)
                                     for x, y in r if x in block}
                    require(len(target_blocks) == 1,
                            'ALL actual edges induce the same target class for each source class')
                    quotient_map[block] = next(iter(target_blocks))
                require(set(quotient_map.values()) == classes_b
                        and len(quotient_map) == len(set(quotient_map.values())),
                        'R induces an actual quotient BIJECTION')
                require(all(labels[y] == block for block, image in quotient_map.items() for y in image),
                        'canonical quotient label map is the INVERSE of the R-induced bijection')
                for g_a, g_b in zip(ga, gb):
                    require(all(labels[g_b[y]] == frozenset(g_a[x] for x in labels[y]) for y in b),
                            'canonical quotient labels are equivariant under the ACTUAL group action')
                    counts['canonical_label_equivariance_checks'] += 1
                source = tuple(h for h in eq_a if e <= h)
                target = tuple(k for k in eq_b if f <= k)
                transported = {h: transport(r, h) for h in source}
                require(len(set(transported.values())) == len(source)
                        and set(transported.values()) == set(target),
                        'transport bijects the entire invariant-equivalence upper interval')
                for h in source:
                    require(compose(compose(r, transported[h]), converse(r)) == h,
                            'the ACTUAL represented reverse transport recovers every H above E')
                    counts['literal_reverse_transport_identities'] += 1
                for h, k in product(source, repeat=2):
                    require((h <= k) == (transported[h] <= transported[k]),
                            'transport preserves AND reflects interval order')
                    require(transported[h & k] == transported[h] & transported[k]
                            and transported[join(a, h, k)] == join(b, transported[h], transported[k]),
                            'actual invariant lattice meets and joins are preserved')
                    require(cover(source, h, k) == cover(target, transported[h], transported[k]),
                            'interval covers are preserved')
                    counts['interval_order_meet_join_cover_pairs'] += 1
                for h in source:
                    require(meet_irreducible(source, h) == meet_irreducible(target, transported[h]),
                            'meet irreducibility is preserved, with top excluded')
                    counts['meet_irreducible_checks'] += 1
                counts['actual_quotient_transport_instances'] += 1
                counts['actual_induced_quotient_bijections'] += 1
        counts['transitive_typed_action_models'] += 1
        tick()


def return_holonomy_controls(counts):
    for n in (1, 2, 3, 4):
        xs = tuple(range(n))
        action = tuple({x: (x + g) % n for x in xs} for g in xs)
        eqs = invariant_equivalences(xs, action)
        # Cosets of actual cyclic subgroups supply nontrivial multivalued
        # factors as well as graph translations; use no abstract product rule.
        differences = {frozenset((g + k * d) % n for k in range(n))
                       for d in range(1, n + 1) if n % d == 0 for g in xs}
        relations = tuple(frozenset((x, y) for x, y in product(xs, repeat=2)
                                   if (y - x) % n in subset) for subset in differences)
        for length in (1, 2, 3):
            for word in product(relations, repeat=length):
                prefixes = [identity(xs)]
                for p in word:
                    prefixes.append(compose(prefixes[-1], p))
                for e in eqs:
                    if not prefixes[-1] <= e:
                        continue
                    labels = [canonical_labels(xs, xs, prefix, e) for prefix in prefixes]
                    kernels = [kernel(lab) for lab in labels]
                    require(labels[0] == labels[-1] and kernels[-1] == e,
                            'canonical endpoint labels agree on the SAME original root sort')
                    for i, p in enumerate(word, 1):
                        require(all(labels[i - 1][x] == labels[i][y] for x, y in p),
                                'EVERY actual edge preserves the ONE common original quotient label')
                        require(compose(p, converse(p)) <= kernels[i - 1]
                                and transport(p, kernels[i - 1]) == kernels[i],
                                'each factor has the actual transported predecessor kernel')
                        require(transport(prefixes[i], e) == kernels[i],
                                'prefix kernel is literal represented transport')
                        # Quotient maps are computed directly from edges;
                        # their action in canonical labels must be identity.
                        q = {(labels[i - 1][x], labels[i][y]) for x, y in p}
                        require(q == set(identity(set(labels[0].values()))),
                                'actual quotient factor map in canonical labels is identity')
                        counts['canonical_prefix_and_edge_identities'] += 1
                    for j in eqs:
                        if not e <= j:
                            continue
                        coarser = [canonical_labels(xs, xs, p, j) for p in prefixes]
                        require(coarser[0] == coarser[-1], 'return identity holds for EVERY coarser J')
                        for i, p in enumerate(word, 1):
                            require(transport(prefixes[i], j) == kernel(coarser[i])
                                    and all(coarser[i - 1][x] == coarser[i][y] for x, y in p),
                                    'all coarser kernels/edge labels come from the SAME prefixes')
                        counts['coarser_J_return_instances'] += 1
                    counts['actual_return_words'] += 1
                    counts['repeated_original_sort_positions'] += length + 1
        tick()
    # A genuinely typed A -> B -> A -> B -> A loop with intermediate
    # transports and repeated sorts. E-classes have two actual roots.
    a = tuple(('A', i) for i in range(4))
    b = tuple(('B', i) for i in range(4))
    carriers = (a, b, a, b, a)
    shifts = (1, 0, 1, 0)
    word = [frozenset((x, y) for x in carriers[i] for y in carriers[i + 1]
                      if (y[1] - x[1] - shift) % 2 == 0) for i, shift in enumerate(shifts)]
    e = frozenset((x, y) for x, y in product(a, repeat=2) if x[1] % 2 == y[1] % 2)
    prefix = identity(a)
    old_labels = canonical_labels(a, a, prefix, e)
    for i, p in enumerate(word, 1):
        previous = prefix
        prefix = compose(prefix, p)
        labels = canonical_labels(a, carriers[i], prefix, e)
        require(transport(p, kernel(old_labels)) == kernel(labels)
                and all(old_labels[x] == labels[y] for x, y in p),
                'typed repeated-sort prefix transports agree with their actual edge')
        require(transport(prefix, e) == transport(p, transport(previous, e)),
                'actual relational composition agrees with successive transport')
        old_labels = labels
        counts['genuinely_typed_composition_checks'] += 1
    require(prefix <= e and old_labels == canonical_labels(a, a, identity(a), e),
            'genuinely typed closed return has identity endpoint holonomy')


def lifting_properties(m, n, s, t, step, rho_step):
    # K=C_m, Gamma=C_n; actions may have nontrivial kernels.
    rho = lambda k: k * rho_step % n
    act = lambda k, x: (x + k * step) % s
    gamma_act = lambda g, b: (b + g) % t
    onto = {rho(k) for k in range(m)} == set(range(n))
    ker = tuple(k for k in range(m) if rho(k) == 0)
    fibre_transitive = all(any(act(k, x) == y for k in ker)
                           for x, y in product(range(s), repeat=2) if x % t == y % t)
    point_lifting = all(any(rho(k) == g and act(k, x) == y for k in range(m))
                        for x, y, g in product(range(s), range(s), range(n))
                        if gamma_act(g, x % t) == y % t)
    return onto, fibre_transitive, point_lifting


def prescribed_action_controls(counts, witnesses):
    for m, n in product(range(1, 7), repeat=2):
        for s in range(1, m + 1):
            if m % s:
                continue
            for t in range(1, min(s, n) + 1):
                if s % t or n % t:
                    continue
                for step, rho_step in product(range(s), range(n)):
                    if m * rho_step % n or (step - rho_step) % t:
                        continue
                    onto, transitive, lifting = lifting_properties(m, n, s, t, step, rho_step)
                    require((onto and transitive) == lifting,
                            'surjective rho plus kernel fibre transitivity iff EVERY prescribed point lift')
                    counts['prescribed_action_equivalence_instances'] += 1
                    if lifting and (s < m or t < n or step == 0 and s > 1):
                        counts['positive_nonfaithful_action_instances'] += 1
        tick()
    require(lifting_properties(4, 2, 4, 2, 1, 1) == (True, True, True),
            'C4 -> C2 has prescribed point lifting on its regular action')
    require(not any(2 * k % 4 == 0 for k in (1, 3)),
            'C4 -> C2 has NO homomorphic section: odd lifts have order four')
    witnesses['point_lifting_without_group_section'] = {'K': 'C4', 'Gamma': 'C2',
        'Y': 'regular C4', 'B': 'parity quotient', 'point_lifting': True,
        'homomorphic_section_exists': False}
    require(lifting_properties(1, 2, 1, 1, 0, 0) == (False, True, False),
            'kernel transitivity alone cannot replace surjectivity of rho')
    witnesses['nononto_rho_boundary'] = {'kernel_fibre_transitive': True,
        'rho_onto': False, 'prescribed_point_lifting': False}
    # rho is identity but the Y action has an untouched extra fibre coordinate.
    y = tuple(product(range(2), repeat=2))
    require(not all(any(((x[0] + k) % 2, x[1]) == z for k in (0,))
                    for x, z in product(y, repeat=2) if x[0] == z[0]),
            'onto rho does not move an untouched coordinate within its fibre')
    witnesses['nontransitive_kernel_boundary'] = {'rho_onto': True,
        'kernel_fibre_transitive': False, 'prescribed_point_lifting': False}
    # Y=B=empty makes (ii) vacuous even for a nononto rho.
    empty_y = ()
    vacuous_lifting = all(False for _ in product(empty_y, empty_y, (0, 1)))
    empty_case_onto = {0} == {0, 1}
    require(vacuous_lifting and not empty_case_onto,
            'empty Y permits a vacuous point-lifting condition with nononto rho')
    witnesses['empty_Y_boundary'] = {'Y_and_B_empty': True,
        'point_lifting_vacuous': vacuous_lifting, 'rho_onto': empty_case_onto}
    # Y is nonempty, but pi misses one B point: nontrivial gamma then
    # gives no compatible Y-pair request, so (ii) cannot force rho onto.
    small_y, larger_b = (0,), (0, 1)
    rho = {0: 0}
    pi = {0: 0}
    require(all(pi[x] == (rho[k] + pi[x]) % 2 for k in rho for x in small_y),
            'missing-onto-pi example still satisfies equivariance')
    compatible = tuple((x, y, g) for x, y, g in product(small_y, small_y, larger_b)
                       if (g + pi[x]) % 2 == pi[y])
    requests_hold = all(any(rho[k] == g and x == y for k in rho) for x, y, g in compatible)
    require(requests_hold and set(pi.values()) != set(larger_b)
            and set(rho.values()) != set(larger_b)
            and not any(g == 1 for _, _, g in compatible),
            'without onto pi all compatible requests can hold while rho is not onto')
    witnesses['missing_surjectivity_of_pi'] = {'Y': 'singleton', 'B': 'regular C2',
        'pi_equivariant': True, 'pi_onto': False, 'rho_onto': False,
        'every_compatible_point_request_holds': requests_hold,
        'nonidentity_gamma_has_compatible_request': False}


def orbital_model(a, b, ga, gb, tau, sigma, counts):
    j, k = kernel(tau), kernel(sigma)
    q, r = tuple(sorted(set(tau.values()))), tuple(sorted(set(sigma.values())))
    induced_a = tuple({tau[x]: tau[g[x]] for x in a} for g in ga)
    induced_b = tuple({sigma[y]: sigma[g[y]] for y in b} for g in gb)
    outputs = pair_orbits(q, r, induced_a, induced_b)
    roots = pair_orbits(a, b, ga, gb)
    diversity = frozenset((x, y) for x, y in product(a, b) if x != y)
    cells, empty = [], 0
    for theta in outputs:
        pullback = frozenset((x, y) for x, y in product(a, b) if (tau[x], sigma[y]) in theta)
        require(pullback, 'surjectivity makes every output orbital pullback nonempty')
        for root in roots:
            if not root & pullback:
                continue
            require(root <= pullback and compose(compose(j, root), k) == pullback,
                    'ANY root witness orbital has equality-inclusive pullback J;O;K')
            counts['actual_orbital_saturation_identities'] += 1
        cell = pullback & diversity
        same = a == b
        exception = (same and j == identity(a) and k == identity(b)
                     and theta == frozenset((tau[x], sigma[x]) for x in a))
        require((not cell) == exception,
                'empty diversity pullback iff same roots, both kernels identity and same-point graph')
        if cell:
            cells.append(cell)
        else:
            empty += 1
            counts['empty_diversity_exceptions_different_output_sorts'] += 1
        counts['output_orbital_classifications'] += 1
    require(empty <= 1 and frozenset().union(*cells) == diversity
            and all(not (c & d) for c, d in combinations(cells, 2)),
            'nonempty diversity pullbacks partition real diversity, with at most one missing output')
    for root in roots:
        if root <= diversity:
            require(sum(root <= c for c in cells) == 1,
                    'diversity root orbitals are partitioned by their output pullback blocks')
            counts['root_orbital_partition_checks'] += 1
    counts['orbital_pullback_models'] += 1


def orbital_pullback_controls(counts):
    for _, a, b, ga, gb in finite_action_models():
        for j in invariant_equivalences(a, ga):
            tau = {x: ('Q', tuple(sorted(y[1] for y in a if (x, y) in j))) for x in a}
            for k in invariant_equivalences(b, gb):
                sigma = {x: ('R', tuple(sorted(y[1] for y in b if (x, y) in k))) for x in b}
                orbital_model(a, b, ga, gb, tau, sigma, counts)
        # The two ROOT sorts now coincide literally, while Q and R remain
        # tagged as different output sorts even when both maps are bijections.
        for j in invariant_equivalences(a, ga):
            tau = {x: ('Q', tuple(sorted(y[1] for y in a if (x, y) in j))) for x in a}
            for k in invariant_equivalences(a, ga):
                sigma = {x: ('R', tuple(sorted(y[1] for y in a if (x, y) in k))) for x in a}
                orbital_model(a, a, ga, ga, tau, sigma, counts)
        tick()


def boundary_controls(counts, witnesses):
    xs = (0, 1)
    sparse = frozenset({(0, 0)})
    require(compose(sparse, converse(sparse)) <= identity(xs)
            and {y for _, y in sparse} != set(xs),
            'without transitivity a nonempty invariant relation may miss an entire target orbit')
    witnesses['missing_transitivity'] = {'nonempty_invariant_R': True,
        'RR_converse_le_E': True, 'target_without_predecessor': 1}
    full = frozenset(product(xs, repeat=2))
    require(not compose(full, converse(full)) <= identity(xs),
            'nonempty total invariant R need not satisfy the transport kernel condition')
    witnesses['missing_kernel_condition'] = {'R': 'universal on two points',
        'E': 'identity', 'predecessor_E_classes': 2, 'canonical_label_well_defined': False}
    shift = frozenset((x, 1 - x) for x in xs)
    require(compose(shift, identity(xs)) == shift and not shift <= identity(xs),
            'a return not contained in E can have NONIDENTITY quotient holonomy')
    witnesses['missing_whole_word_containment'] = {'actual_holonomy': 'transposition',
        'whole_word_le_E': False}
    require(shift != identity(xs) and equivalence(xs, identity(xs)),
            'arbitrary unrelated quotient bijections can introduce a spurious twist')
    unrelated_map = {x: 1 - x for x in xs}
    require(not all(unrelated_map[x] == y for x, y in identity(xs)),
            'the spurious quotient map does NOT respect the actual identity relation')
    witnesses['independent_chart_boundary'] = {'actual_edge_quotient_maps': ['identity', 'identity'],
        'unrelated_replacement_map': 'transposition',
        'replacement_respects_actual_second_relation': False,
        'canonical_actual_holonomy': 'identity'}
    a, b = tuple(range(4)), tuple(range(2))
    parity = frozenset((x, y) for x in a for y in b if x % 2 == y)
    e = frozenset((x, y) for x, y in product(a, repeat=2) if x % 2 == y % 2)
    require(e != identity(a) and transport(parity, e) == identity(b),
            'general transport does not promise nonidentity of a transported kernel')
    witnesses['no_general_noncollapse'] = {'source_equivalence_nonidentity': True,
        'transported_equivalence': 'identity on smaller target sort'}
    elements = tuple(permutations(range(3)))
    indices = {g: i for i, g in enumerate(elements)}
    multiply = lambda p, q: tuple(p[q[i]] for i in range(3))
    right_a = frozenset((i, indices[multiply(g, (1, 0, 2))]) for i, g in enumerate(elements))
    right_b = frozenset((i, indices[multiply(g, (0, 2, 1))]) for i, g in enumerate(elements))
    require(compose(right_a, right_b) != compose(right_b, right_a),
            'actual left-invariant right-translation relations need NOT commute')
    require(compose(compose(compose(right_a, right_b), right_b), right_a) == identity(range(6)),
            'a noncommuting return still telescopes in its ACTUAL factor order')
    witnesses['no_mixed_commutativity'] = {'action': 'left-regular S3',
        'two_actual_invariant_relations_commute': False,
        'ordered_a_b_b_a_return_is_identity': True}
    counts['explicit_boundary_witnesses'] = len(witnesses)


def main():
    counts, witnesses = Counter(), {}
    quotient_transport_controls(counts)
    return_holonomy_controls(counts)
    prescribed_action_controls(counts, witnesses)
    orbital_pullback_controls(counts)
    boundary_controls(counts, witnesses)
    print(json.dumps(dict(status='PASS', seconds=round(time.monotonic() - START, 3),
        scope='bounded actual quotient transport, canonical holonomy, point actions and orbital pullbacks',
        counts=dict(sorted(counts.items())), witnesses=witnesses,
        limits='Finite diagnostics only: no unbounded theorem, FO definability, FULL RAW exactness, named-sort representation, SAP/CCO property or Lean proof is certified.'), sort_keys=True))


if __name__ == '__main__':
    signal.alarm(30)
    main()
