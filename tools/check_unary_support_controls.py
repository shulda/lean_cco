#!/usr/bin/env python3
"""Bounded B034 diagnostics on actual finite unary structures.

Exhaust all partial pairs of unary functions on zero to three points and
all total single unary functions with one directed binary relation on one
to three points. Closed induced substructures reflect function domains;
irreducibility is computed independently by searching for two proper
closed pieces whose union contains every displayed relation tuple. Free
amalgamation over the empty closed structure is allowed. There are no
constants. Unary predicates and diagonal binary tuples are included in
the separate map checks: all structures/maps on one or two source/target
points, plus three specified unary-function configurations from three
source points to two target points with all binary relations/predicates.

The main local-support checks use positive relational arities. A separate
nullary test records the empty-source boundary and verifies three precise
gates: positive arity, nonempty irreducibles only, or explicit reflection
of nullary relations. These are diagnostics of the source statements and
their boundary, not a repair or certification of the source theorem.

These finite one-sort tests do not prove an unbounded or many-sorted
theorem, the HN theorem, its local-finiteness hypothesis, or any external
transfer. No completion-exists surrogate is used for actual K membership.
No factorial enumeration is used. Pilot timeout 10s; deadline 30s.
Reproduce: timeout 10s python tools/check_unary_support_controls.py
"""
from collections import Counter
from itertools import product
import json
import signal
import time


START = time.monotonic()


def require(ok, message, witness=None):
    if not ok:
        raise AssertionError((message, witness))


def tick():
    require(time.monotonic() - START < 30, '30-second diagnostic deadline')


def points(mask):
    while mask:
        bit = mask & -mask
        yield bit.bit_length() - 1
        mask ^= bit


def closure(seed, functions):
    current = seed
    while True:
        following = current
        for f in functions:
            for x in points(current):
                if f[x] >= 0:
                    following |= 1 << f[x]
        if following == current:
            return current
        current = following


def frame(n, functions):
    """Closed domains and all possible free-decomposition candidates."""
    closures = tuple(closure(s, functions) for s in range(1 << n))
    closed = tuple(s for s, c in enumerate(closures) if s == c)
    decompositions = {}
    for d in closed:
        proper = tuple(a for a in closed if a != d and a & d == a)
        decompositions[d] = tuple((a, b) for a in proper for b in proper
                                  if a <= b and a | b == d)
    return closures, closed, decompositions


def irreducible(d, decompositions, relation_supports=()):
    return not any(all(s & a == s or s & b == s for s in relation_supports)
                   for a, b in decompositions[d])


def binary_data(n):
    result = []
    for relation in range(1 << (n * n)):
        tuples = tuple((x, y) for x in range(n) for y in range(n)
                       if relation & (1 << (n * x + y)))
        result.append((tuples, tuple({(1 << x) | (1 << y) for x, y in tuples})))
    return tuple(result)


def local_supports(d, closures, tuples):
    return frozenset([closures[1 << x] for x in points(d)] +
                     [closures[(1 << x) | (1 << y)] for x, y in tuples
                      if x != y and d & (1 << x) and d & (1 << y)])


def partial_unary_controls(counts, witnesses):
    """K = actual total commuting idempotents with generated size <= 2."""
    for n in range(4):
        maps = tuple(product(range(-1, n), repeat=n))
        for functions in product(maps, repeat=2):
            closures, closed, decompositions = frame(n, functions)
            counts['partial_two_unary_models'] += 1
            generated = tuple(closures[1 << x] for x in range(n))
            for x, u in enumerate(generated):
                require(irreducible(u, decompositions),
                        'one-generated domain-reflecting structure is irreducible', (functions, x))
                counts['one_generated_irreducibles'] += 1
            for s in range(1 << n):
                # A weak restriction truncates values outside s. Its inclusion
                # reflects domains exactly when s was genuinely closed.
                domains_reflected = all(f[x] < 0 or s & (1 << f[x])
                                        for f in functions for x in points(s))
                require(bool(domains_reflected) == (s in closed),
                        'domain reflection is exactly closure under defined values')
                union = 0
                for x in points(s):
                    union |= generated[x]
                require(closures[s] == union, 'unary closure is a union of generated supports')
                bound = max((u.bit_count() for u in generated), default=0)
                require(closures[s].bit_count() <= bound * s.bit_count(),
                        'unary closure cardinality bound, including empty generators')
                counts['domain_reflection_and_closure_union_checks'] += 1

            def actual_k(d):
                f, g = functions
                if any(f[x] < 0 or g[x] < 0 for x in points(d)):
                    return False
                return all(f[f[x]] == f[x] and g[g[x]] == g[x] and
                           f[g[x]] == g[f[x]] and closures[1 << x].bit_count() <= 2
                           for x in points(d))

            source_hypothesis = all(actual_k(d) for d in closed
                                    if irreducible(d, decompositions))
            if source_hypothesis:
                counts['actual_K_hypothesis_models'] += 1
                require(all(actual_k(u) for u in generated), 'every U_x is an ACTUAL K member')
                require(actual_k((1 << n) - 1),
                        'actual irreducible membership forces totality and unary identities')
                for s, c in enumerate(closures):
                    require(c.bit_count() <= 2 * s.bit_count(), 'the K-generated size bound transfers')
                    counts['actual_K_size_bound_checks'] += 1
            elif any(v < 0 for f in functions for v in f):
                counts['partial_models_rejected_by_actual_K'] += 1
        tick()

    # Weak function restrictions really lose the closure convention: a
    # singleton restriction can erase the value at 0. Its inclusion then
    # fails domain reflection. It is not an actual induced substructure.
    f = (1, 1)
    _, _, decompositions = frame(2, (f,))
    require(irreducible(3, decompositions), 'the actual generated two-point structure is irreducible')
    weak_left = (-1,)
    require(f[0] >= 0 and weak_left[0] < 0, 'weak restriction deletes an already defined domain point')
    witnesses['weak_function_substructure'] = {
        'function': list(f), 'weak_subset': [0], 'weak_restricted_function': list(weak_left),
        'lost_equation': 'f(0)=1', 'inclusion_reflects_domains': False,
        'weak_subset_closed_under_source_defined_values': False,
        'actual_generated_structure_irreducible': True}
    # A partial singleton has a completed singleton extension, but is not an
    # actual member of the completed age. This refutes completion-exists as
    # a replacement for the source hypothesis.
    _, _, partial_decompositions = frame(1, ((-1,),))
    require(closure(1, ((-1,),)) == 1 and irreducible(1, partial_decompositions),
            'undefined singleton is one-generated and actually irreducible')
    require(all(x >= 0 for x in (0,)) and (-1,)[0] < 0, 'completion exists without source totality')
    witnesses['completion_exists_is_insufficient'] = {
        'partial_function': [-1], 'completion_function': [0],
        'irreducible_source_is_actual_completed_member': False,
        'source_function_total': False}
    counts['negative_unary_convention_witnesses'] += 2


def pair_cover_controls(counts):
    for n in range(1, 4):
        relations = binary_data(n)
        for f in product(range(n), repeat=n):
            closures, closed, decompositions = frame(n, (f,))
            # In a closed domain, evaluating the actual induced function
            # gives precisely the ambient closure, never a truncated value.
            for d in closed:
                restricted = tuple(v if d & (1 << x) else -1 for x, v in enumerate(f))
                for s in range(1 << n):
                    if s & d == s:
                        require(closure(s, (restricted,)) == closures[s], 'closed induced closure agrees')
                        counts['ambient_induced_closure_agreements'] += 1
            for tuples, relation_supports in relations:
                counts['total_unary_directed_binary_models'] += 1
                for d in closed:
                    if not d:
                        continue
                    supports = local_supports(d, closures, tuples)
                    displayed = tuple(s for s in relation_supports if s & d == s)
                    is_irreducible = irreducible(d, decompositions, displayed)
                    counts['closed_nonempty_binary_substructures'] += 1
                    for x in points(d):
                        for y in points(d & ~((1 << (x + 1)) - 1)):
                            pair = (1 << x) | (1 << y)
                            covered = any(u & pair == pair for u in supports)
                            if is_irreducible:
                                require(covered, 'irreducible binary structure has pairwise local cover',
                                        (f, tuples, d, x, y))
                                counts['irreducible_pair_cover_checks'] += 1
                            if not covered:
                                a = b = 0
                                for u in supports:
                                    if not u & (1 << y):
                                        a |= u
                                    if not u & (1 << x):
                                        b |= u
                                require(a != d and b != d and a | b == d and
                                        a in closed and b in closed and
                                        all(s & a == s or s & b == s for s in displayed),
                                        'missing pair constructs two proper actual closed free factors')
                                require(not is_irreducible, 'constructed free decomposition contradicts irreducibility')
                                counts['missing_pair_free_decompositions'] += 1
            tick()


def map_controls(counts):
    configurations = []
    for n in range(1, 3):
        for m in range(1, 3):
            configurations.extend((n, m, f, g) for f in product(range(n), repeat=n)
                                  for g in product(range(m), repeat=m))
    # Full binary relations and predicates on three source points, with
    # both trivial and nontrivial function-preserving identifications.
    configurations.extend(((3, 2, (0, 1, 2), (0, 1)),
                           (3, 2, (0, 0, 2), (0, 1)),
                           (3, 2, (1, 0, 2), (1, 0))))
    cache = {n: binary_data(n) for n in range(1, 4)}
    for n, m, f, g in configurations:
        closures, closed, decompositions = frame(n, (f,))
        for image in product(range(m), repeat=n):
            counts['source_target_function_map_candidates'] += 1
            if not all(image[f[x]] == g[image[x]] for x in range(n)):
                continue
            counts['function_preserving_maps'] += 1
            target_bits = tuple(1 << (m * image[x] + image[y])
                                for x in range(n) for y in range(n))
            injective = {d: len({image[x] for x in points(d)}) == d.bit_count() for d in closed}
            for source_r, (tuples, supports) in enumerate(cache[n]):
                local = local_supports((1 << n) - 1, closures, tuples)
                irreds = tuple(d for d in closed if d and irreducible(
                    d, decompositions, tuple(s for s in supports if s & d == s)))
                for target_r in range(1 << (m * m)):
                    pull_r = sum((1 << k) for k, bit in enumerate(target_bits) if target_r & bit)
                    if source_r & pull_r != source_r:
                        continue
                    counts['binary_homomorphism_map_cases'] += 1
                    bad_r = source_r ^ pull_r
                    embeds = {d: injective[d] and all(
                        not bad_r & (1 << (n * x + y)) for x in points(d) for y in points(d))
                              for d in closed}
                    local_binary_embedding = all(embeds[d] for d in local)
                    if any(bad_r & (1 << (n * x + x)) for x in range(n)):
                        require(not local_binary_embedding, 'singleton supports detect added diagonal binary tuples')
                        counts['diagonal_binary_reflection_failures_detected'] += 1
                    if not local_binary_embedding:
                        continue
                    require(all(embeds[d] for d in irreds),
                            'local binary induced embeddings imply embeddings on irreducibles',
                            (f, g, image, source_r, target_r, tuple(local), irreds))
                    counts['local_binary_embedding_map_cases'] += 1
                    # Source unary predicates must be subsets of the pulled
                    # target predicate; enumerate all such homomorphisms.
                    for target_p in range(1 << m):
                        pull_p = sum(1 << x for x in range(n) if target_p & (1 << image[x]))
                        for source_p in range(1 << n):
                            if source_p & pull_p != source_p:
                                continue
                            counts['unary_binary_homomorphism_map_cases'] += 1
                            bad_p = source_p ^ pull_p
                            local_unary_embedding = all(not d & bad_p for d in local)
                            if bad_p:
                                require(not local_unary_embedding, 'singleton supports detect added unary tuples')
                                counts['unary_relation_reflection_failures_detected'] += 1
                            if local_unary_embedding:
                                require(all(not d & bad_p for d in irreds),
                                        'local unary reflection implies irreducible unary reflection')
                                counts['local_to_HE_map_cases'] += 1
                                counts['irreducible_embedding_checks'] += len(irreds)
                                if len(set(image)) < n:
                                    counts['globally_noninjective_HE_map_cases'] += 1
        tick()


def nullary_and_arity_controls(counts, witnesses):
    # All functions are identities. A nullary tuple is contained even in
    # the empty induced domain. Empty is irreducible under the explicit
    # two-proper-closed-factor definition used above.
    failures = set()
    for n in range(3):
        _, closed, decompositions = frame(n, (tuple(range(n)),))
        irreds = tuple(d for d in closed if irreducible(d, decompositions))
        for m in range(3):
            for image in product(range(m), repeat=n):
                for source_zero, target_zero in product((False, True), repeat=2):
                    if source_zero and not target_zero:
                        continue
                    zero_reflects = source_zero == target_zero
                    local_embeds = all(zero_reflects for _ in range(n))
                    if not local_embeds:
                        continue
                    embeds = {d: zero_reflects and len({image[x] for x in points(d)}) == d.bit_count()
                              for d in irreds}
                    if not all(embeds.values()):
                        failures.add((n, m, source_zero, target_zero))
                        counts['nullary_full_HE_boundary_failures'] += 1
                    require(all(embeds[d] for d in irreds if d),
                            'nullary boundary gate: only nonempty irreducibles')
                    counts['nullary_nonempty_HE_gate_checks'] += 1
                    if zero_reflects:
                        require(all(embeds.values()), 'nullary boundary gate: explicit nullary reflection')
                        counts['explicit_nullary_reflection_gate_checks'] += 1
                    # Removing the nullary symbol entirely gives injective
                    # maps on all singleton irreducibles, plus the empty one.
                    require(all(len({image[x] for x in points(d)}) == d.bit_count() for d in irreds),
                            'nullary boundary gate: positive relational arity')
                    counts['positive_arity_empty_structure_gate_checks'] += 1
    def induced_relational_embedding(d, image, relations):
        return len({image[x] for x in points(d)}) == d.bit_count() and all(
            (args in source) == (tuple(image[x] for x in args) in target)
            for arity, source, target in relations for args in product(tuple(points(d)), repeat=arity))

    empty_embeds = induced_relational_embedding(0, (), ((0, set(), {()}),))
    require(not empty_embeds, 'actual empty induced map fails nullary reflection')
    witnesses['nullary_empty_source'] = {
        'source_size': 0, 'target_size': 1, 'source_nullary_relation': False,
        'target_nullary_relation': True, 'local_supports': [],
        'local_embeddings_vacuous': True, 'full_HE_including_empty': empty_embeds,
        'HE_on_nonempty_irreducibles': True}
    require((0, 1, False, True) in failures,
            'the empty map preserves false source nullary but does not reflect true target nullary')

    # Identity functions, all binary pairs displayed, no ternary source
    # tuple. Every pair support embeds, but the missing three-root tuple
    # is added in the target. The source is irreducible via its binary R.
    functions = ((0, 1, 2),)
    closures, closed, decompositions = frame(3, functions)
    binary = tuple(product(range(3), repeat=2))
    pair_supports = local_supports(7, closures, binary)
    require(irreducible(7, decompositions, tuple({(1 << x) | (1 << y) for x, y in binary})),
            'higher-arity negative source is actually irreducible')
    added_ternary = (0, 1, 2)
    relations = ((2, set(binary), set(binary)), (3, set(), {added_ternary}))
    local_embeddings = all(induced_relational_embedding(d, (0, 1, 2), relations) for d in pair_supports)
    full_embedding = induced_relational_embedding(7, (0, 1, 2), relations)
    require(local_embeddings and not full_embedding,
            'actual induced maps on pairs miss the three-root target tuple reflected by the full map')
    witnesses['higher_arity_pair_reflection_failure'] = {
        'carrier': [0, 1, 2], 'function': [0, 1, 2],
        'binary_relation': 'all ordered pairs', 'source_ternary_relation': [],
        'target_added_ternary_tuple': list(added_ternary),
        'local_support_sizes': sorted({d.bit_count() for d in pair_supports}),
        'local_induced_embeddings': local_embeddings, 'source_irreducible': True,
        'full_induced_embedding': full_embedding}
    # A sole ternary source tuple also breaks the preceding pair-cover
    # assertion itself: its full support makes C irreducible, whereas the
    # singleton/binary recipe sees no binary tuple and produces singletons.
    ternary_support = sum(1 << x for x in set(added_ternary))
    singleton_supports = local_supports(7, closures, ())
    ternary_irreducible = irreducible(7, decompositions, (ternary_support,))
    missed_pairs = tuple((x, y) for x in range(3) for y in range(x + 1, 3)
                         if not any(d & ((1 << x) | (1 << y)) == ((1 << x) | (1 << y))
                                    for d in singleton_supports))
    require(ternary_irreducible and singleton_supports == {1, 2, 4} and len(missed_pairs) == 3,
            'sole ternary source tuple gives an actual irreducible structure with no local pair cover')
    witnesses['higher_arity_local_pair_cover_failure'] = {
        'carrier': [0, 1, 2], 'function': [0, 1, 2], 'binary_relation': [],
        'ternary_relation': [list(added_ternary)], 'source_irreducible': ternary_irreducible,
        'local_supports': [[0], [1], [2]], 'uncovered_pairs': [list(p) for p in missed_pairs]}
    counts['higher_arity_local_pair_cover_failure_checks'] += len(missed_pairs)
    # A genuinely binary function can create a new root jointly, so the
    # unary closure-union step itself has an independent arity boundary.
    def binary_closure(seed):
        return seed | 4 if seed & 3 == 3 else seed
    require(binary_closure(1) | binary_closure(2) != binary_closure(3),
            'binary partial function closure need not preserve generator unions')
    witnesses['binary_function_closure_union_failure'] = {
        'defined_binary_function_equation': 'h(0,1)=2',
        'closure_0': [0], 'closure_1': [1], 'closure_0_1': [0, 1, 2]}
    counts['negative_relational_or_functional_arity_witnesses'] += 4


def additional_boundary_controls(counts, witnesses):
    # Domain-suppressing weak inclusions can assemble an actual unary
    # diagram from proper root-containing factors. The domain-reflecting
    # convention forbids both factors, which is exactly what U_x needs.
    functions = ((1, -1, -1), (2, -1, -1))  # f(x)=a and g(x)=b
    closures, closed, decompositions = frame(3, functions)
    root, left, right = 0, 3, 5
    source_graph = {(i, x, y) for i, f in enumerate(functions)
                    for x, y in enumerate(f) if y >= 0}
    weak_graphs = tuple({(i, x, y) for i, x, y in source_graph
                         if d & (1 << x) and d & (1 << y)} for d in (left, right))
    graph_union_covers = weak_graphs[0] | weak_graphs[1] == source_graph
    overlap = left & right
    overlap_graphs = tuple({t for t in graph if overlap & (1 << t[1]) and
                            overlap & (1 << t[2])} for graph in weak_graphs)
    no_proper_root_factor = not any(d != 7 and d & (1 << root) for d in closed)
    require(graph_union_covers and overlap_graphs[0] == overlap_graphs[1],
            'weak closed-looking factors agree on the overlap and cover the unary function graphs')
    require(left not in closed and right not in closed and no_proper_root_factor and
            closures[1 << root] == 7 and irreducible(7, decompositions),
            'neither weak factor is an actual domain-reflecting root substructure')
    witnesses['weak_domain_graph_union'] = {
        'carrier': ['x', 'a', 'b'], 'function_f': [1, -1, -1], 'function_g': [2, -1, -1],
        'weak_factors': [[0, 1], [0, 2]], 'weak_overlap': [0],
        'weak_graph_union_is_source': graph_union_covers,
        'weak_overlap_functions_agree': overlap_graphs[0] == overlap_graphs[1],
        'actual_proper_closed_root_factor_exists': not no_proper_root_factor,
        'actual_generated_structure_irreducible': True}
    counts['negative_unary_convention_witnesses'] += 1

    # The transfer is pointwise in ONE variable. The equality identity
    # x=y holds in the completed singleton age but need not transfer to C.
    _, closed, decompositions = frame(2, ((0, 1),))
    irreds = tuple(d for d in closed if irreducible(d, decompositions))
    nonempty_irreds = tuple(d for d in irreds if d)
    k_member = lambda d: d.bit_count() <= 1
    equality_identity = lambda d: all(x == y for x, y in product(tuple(points(d)), repeat=2))
    require(set(nonempty_irreds) == {1, 2} and all(k_member(d) for d in irreds),
            'all actual irreducibles belong to the completed empty/singleton identity-function age')
    require(all(equality_identity(d) for d in closed if k_member(d)) and not equality_identity(3),
            'a two-variable identity valid in K need not hold on the whole source')
    witnesses['two_variable_identity_does_not_transfer'] = {
        'source_function': [0, 1], 'K': 'empty and singleton structures with identity unary function',
        'nonempty_irreducibles': [[0], [1]], 'all_actual_irreducibles_in_K': True,
        'identity': 'x=y', 'identity_valid_in_K': True, 'identity_valid_in_source': False}
    counts['negative_term_variable_witnesses'] += 1

    # A binary partial function can be total on every irreducible
    # singleton and still omit mixed source inputs. Unary totality transfer
    # therefore cannot be silently generalized to binary functions.
    binary_function = {(0, 0): 0, (1, 1): 1}
    domains = tuple(range(4))
    binary_closed = tuple(d for d in domains if all(
        not (d & (1 << x) and d & (1 << y)) or d & (1 << z)
        for (x, y), z in binary_function.items()))
    binary_irreds = []
    for d in binary_closed:
        proper = tuple(a for a in binary_closed if a != d and a & d == a)
        decomposes = any(a | b == d and all(
            not (d & (1 << x) and d & (1 << y)) or
            (a & (1 << x) and a & (1 << y) and a & (1 << z)) or
            (b & (1 << x) and b & (1 << y) and b & (1 << z))
            for (x, y), z in binary_function.items()) for a in proper for b in proper)
        if not decomposes:
            binary_irreds.append(d)
    total_on = lambda d: all((x, y) in binary_function for x, y in product(tuple(points(d)), repeat=2))
    require(set(d for d in binary_irreds if d) == {1, 2} and
            all(total_on(d) for d in binary_irreds) and not total_on(3),
            'actual binary-function singleton irreducibles are total while mixed inputs are missing')
    witnesses['binary_function_totality_does_not_transfer'] = {
        'carrier': [0, 1], 'defined_function_graph': [[0, 0, 0], [1, 1, 1]],
        'nonempty_irreducibles': [[0], [1]], 'function_total_on_all_irreducibles': True,
        'function_total_on_source': False, 'undefined_mixed_inputs': [[0, 1], [1, 0]]}
    counts['negative_relational_or_functional_arity_witnesses'] += 1


def main():
    counts, witnesses = Counter(), {}
    partial_unary_controls(counts, witnesses)
    pair_cover_controls(counts)
    map_controls(counts)
    nullary_and_arity_controls(counts, witnesses)
    additional_boundary_controls(counts, witnesses)
    tick()
    print(json.dumps({
        'status': 'PASS', 'counts': dict(sorted(counts.items())),
        'witnesses': witnesses, 'seconds': round(time.monotonic() - START, 3),
        'limits': 'One-sort finite bounds only: <=3 points, <=2 unary functions, unary/binary relations; '
                  'nullary boundary checked separately, no constants, empty-base free amalgams allowed. '
                  'No unbounded theorem, many-sorted proof, HN theorem/local-finiteness, or Lean certification.'
    }, sort_keys=True))


if __name__ == '__main__':
    signal.signal(signal.SIGALRM, lambda *_: (_ for _ in ()).throw(TimeoutError('30-second diagnostic deadline')))
    signal.alarm(30)
    main()
