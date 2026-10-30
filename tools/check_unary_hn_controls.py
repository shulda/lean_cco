#!/usr/bin/env python3
"""Bounded B037 diagnostics on actual unary structures, maps and orders.

The tests independently search closed free decompositions and literal
homomorphism/embedding maps. They exercise pair coverage, partial unary
domains, completed-map rigidity and transport of the SAME map after adding
a universal irreflexive relation. A positive unary-only example remains
globally noninjective across reducible pieces.

Raw one-sorted models with sort predicates independently check that actual
completed membership of every irreducible piece detects malformed point
sorts, function input/output sorts and relation tuples. No claim that an
arbitrary hereditary typed subclass automatically inherits Ramsey is made.

Directed finite orders check acyclicity, injective transport, linear
extension and reflection on already-total source pieces. Equivalence-color
cycles give explicit minimal obstructions showing that binary completeness
and completed singleton closures do not supply a uniform obstruction bound.
No HN/Ramsey theorem, arbitrary-language transfer, infinite class, supplied
obstruction premise, external theorem adapter or Lean proof is certified.
Normal runtime <10s; hard deadline 30s.
Reproduce: timeout 10s python tools/check_unary_hn_controls.py
"""
from collections import Counter
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


def points(mask):
    return tuple(x for x in range(mask.bit_length()) if mask & (1 << x))


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
    closures = tuple(closure(s, functions) for s in range(1 << n))
    closed = tuple(s for s in range(1 << n) if closures[s] == s)
    decompositions = {}
    for d in closed:
        proper = tuple(a for a in closed if a != d and a & d == a)
        decompositions[d] = tuple((a, b) for a in proper for b in proper
                                  if a <= b and a | b == d)
    return closures, closed, decompositions


def relation_supports(relations, domain):
    return tuple({sum(1 << x for x in set(args))
                  for relation in relations for args in relation
                  if all(domain & (1 << x) for x in args)})


def irreducible(d, decompositions, relations=()):
    supports = relation_supports(relations, d)
    return not any(all(s & a == s or s & b == s for s in supports)
                   for a, b in decompositions[d])


def all_binary_relations(n):
    entries = tuple(product(range(n), repeat=2))
    for mask in range(1 << len(entries)):
        yield frozenset(e for i, e in enumerate(entries) if mask & (1 << i))


def graph_relation(n, mask):
    pairs = tuple(combinations(range(n), 2))
    return frozenset((u, v) for i, pair in enumerate(pairs) if mask & (1 << i)
                     for u, v in (pair, pair[::-1]))


def full_irreflexive(n):
    return frozenset((x, y) for x in range(n) for y in range(n) if x != y)


def is_homomorphism(source_functions, source_relations, target_functions,
                    target_relations, image):
    return all(f[x] < 0 or g[image[x]] == image[f[x]]
               for f, g in zip(source_functions, target_functions) for x in range(len(image))) and all(
        tuple(image[x] for x in args) in target
        for source, target in zip(source_relations, target_relations) for args in source)


def is_embedding(domain, source_functions, source_relations, target_functions,
                 target_relations, image):
    vertices = points(domain)
    if len({image[x] for x in vertices}) != len(vertices):
        return False
    if any((f[x] < 0) != (g[image[x]] < 0) or
           (f[x] >= 0 and image[f[x]] != g[image[x]])
           for f, g in zip(source_functions, target_functions) for x in vertices):
        return False
    return all((args in source) == (tuple(image[x] for x in args) in target)
               for source, target in zip(source_relations, target_relations)
               for args in product(vertices, repeat=2))


def is_he(n, source_functions, source_relations, target_functions,
          target_relations, image, cached_frame=None):
    if not is_homomorphism(source_functions, source_relations, target_functions,
                          target_relations, image):
        return False
    _, closed, decompositions = cached_frame or frame(n, source_functions)
    return all(is_embedding(d, source_functions, source_relations,
                            target_functions, target_relations, image)
               for d in closed if irreducible(d, decompositions, source_relations))


def pair_and_edge_closure_controls(counts):
    for n in range(4):
        functions = tuple(product(range(n), repeat=n))
        for f in functions:
            closures, closed, decompositions = frame(n, (f,))
            for relation in all_binary_relations(n):
                counts['total_unary_binary_models'] += 1
                for d in closed:
                    vertices = points(d)
                    covered = all(closures[1 << x] & (1 << y) or
                                  closures[1 << y] & (1 << x) or
                                  (x, y) in relation or (y, x) in relation
                                  for x, y in combinations(vertices, 2))
                    if covered:
                        require(irreducible(d, decompositions, (relation,)),
                                'positive unary-or-binary pair coverage implies actual irreducibility')
                        counts['covered_induced_irreducible_pieces'] += 1
        # The separate displayed-edge argument allows initially partial
        # maps and includes diagonal E tuples. Its conclusion is about the
        # actual generated closure, not merely its two root points.
        for f in product(range(-1, n), repeat=n):
            closures, _, decompositions = frame(n, (f,))
            for x, y in product(range(n), repeat=2):
                d = closures[(1 << x) | (1 << y)]
                require(irreducible(d, decompositions, (frozenset({(x, y)}),)),
                        'the closed support of any displayed E tuple is irreducible, including loops')
                counts['partial_unary_displayed_edge_supports'] += 1
        tick()


def partial_admissibility_controls(counts, witnesses):
    # This concrete K has total commuting idempotent maps and singleton
    # generated closures of size at most two. Membership is tested on the
    # EXISTING induced diagram, never by finding a later completion.
    for n in range(4):
        maps = tuple(product(range(-1, n), repeat=n))
        for functions in product(maps, repeat=2):
            f, g = functions
            closures, closed, decompositions = frame(n, functions)
            generated = tuple(closures[1 << x] for x in range(n))
            counts['partial_two_unary_models'] += 1
            for u in generated:
                require(irreducible(u, decompositions),
                        'a domain-reflecting actual unary singleton closure is irreducible')
                counts['partial_one_generated_irreducibility_checks'] += 1

            def actual_k(d):
                vertices = points(d)
                return all(f[x] >= 0 and g[x] >= 0 for x in vertices) and all(
                    f[f[x]] == f[x] and g[g[x]] == g[x] and f[g[x]] == g[f[x]] and
                    closures[1 << x].bit_count() <= 2 for x in vertices)

            if all(actual_k(d) for d in closed if irreducible(d, decompositions)):
                require(all(actual_k(u) for u in generated), 'every actual singleton closure belongs to K')
                require(all(value >= 0 for f in functions for value in f),
                        'the actual local condition forces global intended unary totality')
                require(all(f[g[x]] == g[f[x]] for x in range(n)), 'one-variable identities transfer')
                for seed, cl in enumerate(closures):
                    require(cl.bit_count() <= 2 * seed.bit_count(), 'conditional generated-size bound')
                    counts['admissible_finite_generator_bounds'] += 1
                counts['actual_irreducible_K_hypothesis_models'] += 1
            tick()
    witnesses['mere_completability_is_not_admissibility'] = {
        'partial_singleton_function': [-1], 'possible_completion': [0],
        'existing_closure_is_actual_completed_member': False}
    require(closure(1, ((-1,),)) == 1 and (-1,)[0] < 0,
            'a completable partial singleton still has an undefined original value')


def universal_edge_controls(counts, witnesses):
    # K is the complete irreflexive graph age with identity unary function.
    # Every member is irreducible, so old completed HE maps are embeddings.
    # Source graphs are independent partial old-R / new-E diagrams.
    for n in range(4):
        identity = tuple(range(n))
        cached = frame(n, (identity,))
        _, closed, decompositions = cached
        graph_count = 1 << (n * (n - 1) // 2)
        for old_mask, edge_mask in product(range(graph_count), repeat=2):
            old, edge = graph_relation(n, old_mask), graph_relation(n, edge_mask)

            def actual_k_star(d):
                vertices = points(d)
                complete = frozenset((x, y) for x in vertices for y in vertices if x != y)
                return (frozenset(p for p in old if p[0] in vertices and p[1] in vertices) == complete and
                        frozenset(p for p in edge if p[0] in vertices and p[1] in vertices) == complete)

            if not all(actual_k_star(d) for d in closed
                       if irreducible(d, decompositions, (old, edge))):
                counts['expanded_local_hypothesis_rejections'] += 1
                continue
            counts['expanded_local_hypothesis_models'] += 1
            for m in range(4):
                target_f, target_rel = tuple(range(m)), full_irreflexive(m)
                for image in product(range(m), repeat=n):
                    if is_he(n, (identity,), (old,), (target_f,), (target_rel,), image, cached):
                        require(is_he(n, (identity,), (old, edge), (target_f,),
                                      (target_rel, target_rel), image, cached),
                                'the SAME old HE vertex map is an expanded HE map')
                        for d in closed:
                            if irreducible(d, decompositions, (old, edge)):
                                require(is_embedding(d, (identity,), (old,), (target_f,),
                                                     (target_rel,), image),
                                        'old restriction on an expanded irreducible completed piece embeds')
                                counts['same_map_local_reflection_checks'] += 1
                        counts['same_map_universal_edge_HE_checks'] += 1
                        if len(set(image)) != n:
                            counts['same_map_globally_noninjective_checks'] += 1
        tick()

    # Unary-only K: empty/single finite cycles are hereditary and each is
    # irreducible, although no old binary relation covers the point pairs.
    f, target_f, image = (1, 0, 3, 2), (1, 0), (0, 1, 0, 1)
    edge = frozenset({(0, 1), (1, 0), (2, 3), (3, 2)})
    _, closed, decompositions = frame(4, (f,))
    irreds = tuple(d for d in closed if irreducible(d, decompositions, (edge,)))
    require(set(irreds) == {0, 3, 12}, 'expanded irreducibles are exactly the completed unary cycles')
    require(is_he(4, (f,), (), (target_f,), (), image), 'unary-only old map is HE')
    require(is_he(4, (f,), (edge,), (target_f,), (full_irreflexive(2),), image),
            'unary-generated irreducibility also supplies same-map expanded HE')
    require(len(set(image)) < len(image), 'the positive unary example is globally noninjective')
    witnesses['unary_only_rigidity_with_global_collisions'] = {
        'source_function': list(f), 'target_function': list(target_f), 'same_vertex_map': list(image),
        'old_binary_relations': [], 'expanded_nonempty_irreducibles': [[0, 1], [2, 3]],
        'old_HE': True, 'expanded_HE': True, 'globally_injective': False}

    # Without completed-map rigidity the old empty language sees only
    # singleton irreducibles, so a constant HE can collapse a displayed E.
    old_image, edge = (0, 0), full_irreflexive(2)
    require(is_he(2, (), (), (), (), old_image), 'empty-language constant map is an old HE')
    require(not is_he(2, (), (edge,), (), (frozenset(),), old_image),
            'the same collapsed map does not preserve an irreflexive edge')
    require(is_he(2, (), (edge,), (), (edge,), (0, 1)),
            'an alternative injective expanded completion exists')
    witnesses['completed_map_rigidity_is_necessary'] = {
        'source_vertices': [0, 1], 'target_vertices': [0], 'old_language': 'empty',
        'same_constant_vertex_map': list(old_image), 'old_HE': True, 'expanded_HE': False,
        'different_injective_completion_exists': True}
    _, closed, decompositions = frame(1, ())
    require(irreducible(1, decompositions, (frozenset({(0, 0)}),)), 'loop support is irreducible')
    require(frozenset({(0, 0)}) != full_irreflexive(1),
            'actual K-star membership rejects a displayed diagonal E loop')
    witnesses['diagonal_edge_rejected_by_actual_local_membership'] = {
        'source_E': [[0, 0]], 'generated_support_irreducible': True,
        'support_is_actual_K_star_member': False}


def topological_order(n, edges):
    pending = set(range(n))
    answer = []
    while pending:
        ready = sorted(x for x in pending if not any(y in pending and (y, x) in edges for y in pending))
        if not ready:
            return None
        for x in ready:
            pending.remove(x)
            answer.append(x)
    return tuple(answer)


def raw_sort_guard_controls(counts, witnesses):
    # The unrestricted HN ambient signature can encode S,T as unary
    # predicates. A completed intended object has exactly one tag per
    # point, F defined exactly on S with values in T, and R contained in
    # S x T. Source raw objects are not assumed to satisfy any of this.
    def actual_typed(d, tags, f, relation):
        vertices = points(d)
        return all(tags[x] in (1, 2) for x in vertices) and all(
            (f[x] >= 0) == (tags[x] == 1) and
            (f[x] < 0 or (d & (1 << f[x]) and tags[f[x]] == 2)) for x in vertices) and all(
            tags[x] == 1 and tags[y] == 2 for x, y in relation
            if d & (1 << x) and d & (1 << y))

    for n in range(3):
        for f in product(range(-1, n), repeat=n):
            closures, closed, decompositions = frame(n, (f,))
            for tags in product(range(4), repeat=n):
                sort_s = frozenset((x,) for x in range(n) if tags[x] & 1)
                sort_t = frozenset((x,) for x in range(n) if tags[x] & 2)
                for relation in all_binary_relations(n):
                    relations = (sort_s, sort_t, relation)
                    irreds = tuple(d for d in closed if irreducible(d, decompositions, relations))
                    local_condition = all(actual_typed(d, tags, f, relation) for d in irreds)
                    require(local_condition == actual_typed((1 << n) - 1, tags, f, relation),
                            'raw malformed typing is detected by actual completed irreducible diagrams')
                    for x in range(n):
                        u = closures[1 << x]
                        require(irreducible(u, decompositions, relations),
                                'the actual point-generated piece is irreducible in the raw language')
                        bad_point = tags[x] not in (1, 2)
                        bad_function = ((f[x] >= 0) != (tags[x] == 1) or
                                        (f[x] >= 0 and tags[f[x]] != 2))
                        if bad_point or bad_function:
                            require(not actual_typed(u, tags, f, relation),
                                    'ill-sorted point or unary equation cannot lie in an actual typed member')
                            counts['raw_illtyped_point_or_function_local_rejections'] += 1
                        if f[x] >= 0:
                            require(closures[(1 << x) | (1 << f[x])] == u,
                                    'a displayed unary function graph has the actual one-generated support')
                    for x, y in relation:
                        support = closures[(1 << x) | (1 << y)]
                        require(irreducible(support, decompositions, relations),
                                'every displayed relation tuple has an irreducible actual closed support')
                        if tags[x] != 1 or tags[y] != 2:
                            require(not actual_typed(support, tags, f, relation),
                                    'an ill-sorted relation tuple cannot hide outside all irreducible pieces')
                            counts['raw_illtyped_relation_local_rejections'] += 1
                    counts['raw_one_sorted_typed_guard_models'] += 1
                    if local_condition:
                        counts['raw_models_accepted_as_actual_typed'] += 1
        tick()
    examples = (
        ('missing_sort', (0,), (-1,), frozenset(), 0),
        ('multiple_sorts', (3,), (0,), frozenset(), 0),
        ('wrong_function_source', (2, 2), (1, -1), frozenset(), 0),
        ('wrong_function_target', (1, 1), (1, 1), frozenset(), 0),
        ('missing_intended_function_domain', (1, 2), (-1, -1), frozenset(), 0),
        ('illtyped_relation', (1, 2), (1, -1), frozenset({(1, 0)}), None),
    )
    checked = []
    for name, tags, f, relation, root in examples:
        n = len(tags)
        closures, _, decompositions = frame(n, (f,))
        seed = 1 << root if root is not None else sum(1 << x for x in {v for p in relation for v in p})
        support = closures[seed]
        require(irreducible(support, decompositions, (relation,)) and
                not actual_typed(support, tags, f, relation),
                'the explicit malformed diagram has an actual irreducible witness', name)
        checked.append({'defect': name, 'point_tags': list(tags), 'F': list(f),
                        'R': sorted(map(list, relation)), 'closed_irreducible_support': list(points(support)),
                        'actual_completed_typed_member': False})
    witnesses['raw_one_sorted_typing_is_forced_locally'] = {
        'intended_signature': 'disjoint exhaustive S,T; F:S->T total; R subset SxT',
        'ambient_language': 'raw one-sorted partial F with unary sort predicates',
        'malformed_examples': checked,
        'arbitrary_typed_hereditary_subclass_Ramsey_claimed': False}


def order_controls(counts, witnesses):
    # All literal maps into finite strict linear orders, including maps
    # identifying incomparable vertices. A directed closed walk would
    # have to map to a strict increasing cycle, which these tests reject.
    for n in range(4):
        for edges in all_binary_relations(n):
            acyclic = topological_order(n, edges) is not None
            for m in range(4):
                for image in product(range(m), repeat=n):
                    preserves = all(image[x] < image[y] for x, y in edges)
                    if preserves:
                        require(acyclic, 'a homomorphism to a strict linear order forces acyclicity')
                        counts['strict_order_homomorphism_acyclicity_checks'] += 1
                        if len(set(image)) < n:
                            counts['noninjective_order_homomorphisms'] += 1
        tick()
    for n in range(5):
        directed = tuple((x, y) for x in range(n) for y in range(n) if x != y)
        for mask in range(1 << len(directed)):
            edges = frozenset(e for i, e in enumerate(directed) if mask & (1 << i))
            if topological_order(n, edges) is None:
                continue
            # Exhaust literal injections into n+1 points. One extra point
            # represents a completed host vertex outside the source image.
            for image in permutations(range(n + 1), n):
                transported = frozenset((image[x], image[y]) for x, y in edges)
                linear = topological_order(n + 1, transported)
                require(linear is not None, 'injective transport keeps displayed order acyclic')
                rank = {x: i for i, x in enumerate(linear)}
                require(all(rank[image[x]] < rank[image[y]] for x, y in edges),
                        'linear extension retains every displayed source comparison')
                for d in range(1 << n):
                    vertices = points(d)
                    if all((x, y) in edges or (y, x) in edges for x, y in combinations(vertices, 2)):
                        require(all(((x, y) in edges) == (rank[image[x]] < rank[image[y]])
                                    for x, y in product(vertices, repeat=2)),
                                'already-total ordered source pieces reflect the final order')
                        counts['completed_order_piece_reflection_checks'] += 1
                counts['injective_order_transport_and_extension_checks'] += 1
            tick()
    source_order, collapsed = frozenset({(0, 1), (1, 2)}), (0, 1, 0)
    image_edges = frozenset((collapsed[x], collapsed[y]) for x, y in source_order)
    require(topological_order(3, source_order) is not None and topological_order(2, image_edges) is None,
            'noninjective old completion can create an order cycle during transport')
    witnesses['noninjective_order_transport_can_create_cycle'] = {
        'source_order_edges': [[0, 1], [1, 2]], 'old_vertex_map': list(collapsed),
        'transported_edges': sorted(map(list, image_edges)), 'source_acyclic': True,
        'transported_acyclic': False, 'scope': 'transport mechanism, not a counterexample to the HN theorem'}
    require(is_he(2, (), (frozenset(),), (), (frozenset({(0, 1)}),), (0, 1)),
            'injective HE completion may add order on an initially reducible source')
    require(not is_embedding(3, (), (frozenset(),), (), (frozenset({(0, 1)}),), (0, 1)),
            'injective HE is not a globally induced embedding')
    witnesses['injective_HE_need_not_be_global_embedding'] = {
        'source_order': [], 'target_order': [[0, 1]], 'vertex_map': [0, 1],
        'injective_HE': True, 'globally_induced_embedding': False}


def components(vertices, edges):
    unseen = set(vertices)
    groups = []
    while unseen:
        seed = min(unseen)
        reached = {seed}
        while True:
            following = reached | {y for x in reached for y in unseen if (x, y) in edges or (y, x) in edges}
            if following == reached:
                break
            reached = following
        groups.append(frozenset(reached))
        unseen -= reached
    return tuple(groups)


def obstruction_controls(counts, witnesses):
    # K has complete binary colors R=(distinct equivalent) and
    # B=(inequivalent). The all-size mathematical family is an R path
    # closed by one B edge. We check its actual finite instances only.
    family = []
    for n in range(4, 8):
        red = frozenset((u, v) for x in range(n - 1) for u, v in ((x, x + 1), (x + 1, x)))
        blue = frozenset({(0, n - 1), (n - 1, 0)})
        _, closed, decompositions = frame(n, ())
        irreds = tuple(d for d in closed if irreducible(d, decompositions, (red, blue)))
        for d in irreds:
            vertices = points(d)
            for x, y in permutations(vertices, 2):
                require(((x, y) in red) != ((x, y) in blue),
                        'every irreducible source piece already has a complete one-color-per-pair diagram')
            require(len(vertices) <= 2, 'the long cycle has no larger irreducible piece')
            counts['obstruction_actual_completed_irreducible_checks'] += 1
        whole_components = components(range(n), red)
        require(len(whole_components) == 1 and (0, n - 1) in blue,
                'R-path transitivity contradicts B endpoints in EVERY K homomorphism completion')
        require(all(closure(1 << x, ()) == 1 << x for x in range(n)),
                'all singleton closures are actual completed singleton members')
        for d in closed:
            if d == (1 << n) - 1:
                continue
            vertices = points(d)
            groups = components(vertices, red)
            red_completion = frozenset((x, y) for group in groups for x, y in permutations(group, 2))
            blue_completion = frozenset((x, y) for x, y in permutations(vertices, 2)
                                        if (x, y) not in red_completion)
            require(all(p in red_completion for p in red if p[0] in vertices and p[1] in vertices),
                    'proper-subset equivalence completion preserves all displayed R tuples')
            require(all(p in blue_completion for p in blue if p[0] in vertices and p[1] in vertices),
                    'removing any point breaks the contradictory R path between B endpoints')
            image = tuple(range(n))
            require(all(is_embedding(i, (), (red, blue), (), (red_completion, blue_completion), image)
                        for i in irreds if i & d == i),
                    'identity completion reflects every irreducible piece of the proper restriction')
            counts['proper_obstruction_restrictions_completed'] += 1
        family.append({'vertices': n, 'minimal_noncompletable': True,
                       'all_irreducibles_actual_completed': True, 'all_singleton_closures_completed': True})
        counts['minimal_equivalence_color_obstructions'] += 1
        tick()
    witnesses['binary_coverage_does_not_supply_obstruction_bound'] = {
        'K': 'finite complete equivalence-color networks R=same class distinct, B=different classes',
        'source': 'R path with B joining its endpoints', 'checked_instances': family,
        'boundedness_premise_is_a_separate_input': True,
        'scope': 'finite minimal obstruction diagnostics; no general HN/Ramsey assertion'}


def main():
    counts, witnesses = Counter(), {}
    pair_and_edge_closure_controls(counts)
    partial_admissibility_controls(counts, witnesses)
    universal_edge_controls(counts, witnesses)
    raw_sort_guard_controls(counts, witnesses)
    order_controls(counts, witnesses)
    obstruction_controls(counts, witnesses)
    print(json.dumps({'status': 'PASS', 'seconds': round(time.monotonic() - START, 3),
                      'counts': dict(sorted(counts.items())), 'witnesses': witnesses,
                      'limits': 'Finite one-sort diagnostics do not certify arbitrary languages, HN/Ramsey, uniform obstruction premises, external adapters or Lean.'},
                     sort_keys=True))


if __name__ == '__main__':
    signal.signal(signal.SIGALRM, lambda *_: (_ for _ in ()).throw(TimeoutError('30-second deadline')))
    signal.alarm(30)
    main()
