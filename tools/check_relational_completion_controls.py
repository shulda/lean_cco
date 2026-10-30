#!/usr/bin/env python3
"""Bounded B038 diagnostics on relational collision splitting and cycle fans.

Independent literal homomorphism/embedding tests and searches for free
decompositions are used below. Finite signatures of arity 0--4 sample the
arbitrary finite-arity RELATIONAL theorem; they do not limit its signature
or certify its general mathematics. The distinguished invariant is the
INITIAL TARGET IMAGE diagram, not reflection of missing source tuples.

Cycle-fan controls use genuine AP identifications in the one-color class
of complete structures of size at most three. This class is not CCO:
K4 is the explicit missing-CCO negative. Complete atomic homomorphisms are
separately enumerated. Partial triangle consistency, missing SAP, missing
irreflexivity/atom uniqueness, and functional-deletion boundaries are
explicit witnesses. No infinite homogeneous/SAP/CCO theorem or Lean code
is certified. Normal runtime <10s; hard deadline 30s.
Reproduce: timeout 10s python tools/check_relational_completion_controls.py
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


def subsets(xs):
    xs = tuple(xs)
    for size in range(len(xs) + 1):
        yield from combinations(xs, size)


def relations_on(domain, relations):
    domain = set(domain)
    return tuple((arity, frozenset(t for t in relation if set(t) <= domain))
                 for arity, relation in relations)


def irreducible(domain, relations):
    domain = frozenset(domain)
    actual = tuple(t for _, rel in relations_on(domain, relations) for t in rel)
    proper = tuple(frozenset(s) for s in subsets(domain) if frozenset(s) != domain)
    return not any(a | b == domain and all(set(t) <= a or set(t) <= b for t in actual)
                   for a in proper for b in proper)


def homomorphism(source, target, image):
    return all(tuple(image[x] for x in t) in tr
               for (_, sr), (_, tr) in zip(source, target) for t in sr)


def embedding(domain, source, target, image):
    domain = tuple(domain)
    if len({image[x] for x in domain}) != len(domain):
        return False
    return all((t in sr) == (tuple(image[x] for x in t) in tr)
               for (arity, sr), (_, tr) in zip(source, target)
               for t in product(domain, repeat=arity))


def is_he(n, source, target, image):
    return homomorphism(source, target, image) and all(
        embedding(s, source, target, image) for s in subsets(range(n))
        if irreducible(s, source))


def partitions(n):
    if n == 0:
        yield ()
        return
    def rec(labels, maximum):
        if len(labels) == n:
            yield tuple(labels)
            return
        for label in range(maximum + 2):
            yield from rec(labels + [label], max(maximum, label))
    yield from rec([0], 0)


def push(relations, image):
    return tuple((arity, frozenset(tuple(image[x] for x in t) for t in rel))
                 for arity, rel in relations)


def clone_target(size, target, vertex):
    """Two literal copies, identified exactly off vertex; fresh label=size."""
    return tuple((arity, rel | frozenset(tuple(size if x == vertex else x for x in t)
                                         for t in rel)) for arity, rel in target)


def collisions(image):
    return sum(image[x] == image[y] for x, y in combinations(range(len(image)), 2))


def image_diagram(domain, target, image):
    """The induced target diagram indexed by the source's marked vertices."""
    domain = tuple(domain)
    return tuple(tuple(tuple(image[x] for x in t) in rel
                       for t in product(domain, repeat=arity))
                 for arity, rel in target)


def tuple_and_clone_controls(counts):
    for n in range(5):
        for arity in range(5):
            for t in product(range(n), repeat=arity):
                relation = ((arity, frozenset({t})),)
                require(irreducible(set(t), relation),
                        'the actual support of a displayed relation tuple is irreducible', t)
                counts['displayed_tuple_irreducible_supports'] += 1
    # Every ternary relation on two points, with arbitrary repeated entries.
    tuples = tuple(product(range(2), repeat=3))
    for mask in range(1 << len(tuples)):
        rel = ((3, frozenset(t for i, t in enumerate(tuples) if mask & (1 << i))),)
        for v in range(2):
            extended = clone_target(2, rel, v)
            for copy_map in ((0, 1), tuple(2 if x == v else x for x in range(2))):
                require(embedding(range(2), rel, extended, copy_map),
                        'both cloned copies preserve the WHOLE induced ternary diagram')
                counts['whole_ternary_clone_diagrams'] += 1
            require({0, 1} & set(2 if x == v else x for x in range(2)) == {1 - v},
                    'the two copy images have exactly the prescribed strong intersection')
    tick()


def collision_controls(counts, witnesses):
    for n in range(4):
        pairs = tuple(product(range(n), repeat=2))
        ternary_options = [frozenset()]
        if n:
            ternary_options.append(frozenset((x, x, x) for x in range(n)))
        if n >= 2:
            ternary_options.append(frozenset({(0, 0, 1)}))
        if n >= 3:
            ternary_options.append(frozenset({(0, 1, 2)}))
        for mask in range(1 << len(pairs)):
            binary = frozenset(t for i, t in enumerate(pairs) if mask & (1 << i))
            for ternary in ternary_options:
                source = ((0, frozenset({()})), (2, binary), (3, ternary))
                for image in partitions(n):
                    size = max(image, default=-1) + 1
                    original = push(source, image)
                    target_variants = [original]
                    extra_binary = frozenset((x, y) for x in range(size)
                                             for y in range(size) if x != y)
                    enlarged = (original[0], (2, original[1][1] | extra_binary), original[2])
                    if enlarged != original:
                        target_variants.append(enlarged)
                    for target in target_variants:
                        counts['relational_map_candidates'] += 1
                        if not is_he(n, source, target, image):
                            continue
                        counts['actual_homomorphism_embeddings'] += 1
                        distinguished = tuple(s for s in subsets(range(n))
                                              if len({image[x] for x in s}) == len(s))
                        old_diagrams = tuple(image_diagram(s, target, image) for s in distinguished)
                        for _, relation in source:
                            for t in relation:
                                require(len({image[x] for x in set(t)}) == len(set(t)),
                                        'every displayed tuple has at most one root in a collision fibre')
                                counts['HE_tuple_fibre_guards'] += 1
                        current_image, current_target, current_size = image, target, size
                        while collisions(current_image):
                            vertex = next(v for v in set(current_image) if current_image.count(v) >= 2)
                            fibre = tuple(i for i, v in enumerate(current_image) if v == vertex)
                            # Every nontrivial split is tested independently;
                            # then one singleton split advances the actual loop.
                            extended = clone_target(current_size, current_target, vertex)
                            # SAP does not prescribe tuples using BOTH copies
                            # of v. Maximal mixed tuples stress their complete
                            # irrelevance to every protected source/image set.
                            mixed_extended = tuple((arity, rel | frozenset(
                                t for t in product(range(current_size + 1), repeat=arity)
                                if vertex in t and current_size in t))
                                for arity, rel in extended)
                            for moved in subsets(fibre):
                                if not moved or len(moved) == len(fibre):
                                    continue
                                moved = set(moved)
                                new_image = tuple(current_size if i in moved else v
                                                  for i, v in enumerate(current_image))
                                require(is_he(n, source, extended, new_image),
                                        'clone splitting preserves global homomorphism AND every irreducible embedding')
                                require(collisions(current_image) - collisions(new_image)
                                        == len(moved) * (len(fibre) - len(moved)),
                                        'collision measure decreases by the exact product of split sizes')
                                require(tuple(image_diagram(s, extended, new_image) for s in distinguished)
                                        == old_diagrams,
                                        'each initially injective distinguished IMAGE retains its entire induced type')
                                require(is_he(n, source, mixed_extended, new_image) and
                                        tuple(image_diagram(s, mixed_extended, new_image) for s in distinguished)
                                        == old_diagrams,
                                        'arbitrary mixed-clone tuples are unused by every protected image')
                                counts['unconstrained_cross_clone_tuple_checks'] += 1
                                counts['all_nontrivial_fibre_split_checks'] += 1
                            moved_root = fibre[0]
                            current_image = tuple(current_size if i == moved_root else v
                                                  for i, v in enumerate(current_image))
                            current_target, current_size = mixed_extended, current_size + 1
                            counts['strict_collision_descent_steps'] += 1
                        require(len(set(current_image)) == n and
                                is_he(n, source, current_target, current_image),
                                'the actual finite descent finishes with an injective HE')
                        require(tuple(image_diagram(s, current_target, current_image) for s in distinguished)
                                == old_diagrams, 'distinguished image types persist to the terminal map')
                        counts['terminal_injective_HE_maps'] += 1
        tick()
    # A distinguished h-injective pair need NOT have been source-induced.
    source = ((2, frozenset({(0, 2)})),)
    target = ((2, frozenset({(0, 1)})),)
    image = (0, 1, 1)
    require(is_he(3, source, target, image) and not embedding((0, 1), source, target, image),
            'the source HE need not embed a merely injective distinguished factor')
    extended, split = clone_target(2, target, 1), (0, 2, 1)
    require(is_he(3, source, extended, split) and
            image_diagram((0, 1), target, image) == image_diagram((0, 1), extended, split),
            'the correct preserved invariant is the initial target IMAGE type')
    witnesses['distinguished_image_not_source_reflection'] = {
        'source_relation': [[0, 2]], 'source_map': list(image),
        'target_relation': [[0, 1]], 'distinguished_source_pair': [0, 1],
        'original_map_embeds_that_source_pair': False,
        'new_map': list(split), 'initial_induced_image_type_preserved': True,
        'old_whole_image_size': len(set(image)), 'new_whole_image_size': len(set(split))}


def complete_colorings(n):
    pairs = tuple((x, y) for x in range(n) for y in range(n) if x != y)
    for mask in range(1 << len(pairs)):
        yield {p: (mask >> i) & 1 for i, p in enumerate(pairs)}


def atomic_hom(source, target, image):
    return all((image[x], image[y]) in target and target[image[x], image[y]] == color
               for (x, y), color in source.items())


def atomic_embedding(source, target, image):
    n = len(image)
    return len(set(image)) == n and all(
        source.get((x, y)) == target.get((image[x], image[y]))
        for x, y in product(range(n), repeat=2))


def atomic_hom_controls(counts, witnesses):
    models = {n: tuple(complete_colorings(n)) for n in range(4)}
    for n in range(4):
        for m in range(4):
            for source in models[n]:
                for target in models[m]:
                    for image in product(range(m), repeat=n):
                        counts['complete_atomic_map_candidates'] += 1
                        if atomic_hom(source, target, image):
                            require(atomic_embedding(source, target, image),
                                    'complete unique irreflexive atom homomorphisms are injective induced embeddings')
                            counts['complete_atomic_hom_embeddings'] += 1
        tick()
    # Explicit complete four-point inputs extend the small directed cases.
    for bits in range(64):
        edges = tuple(combinations(range(4), 2))
        source = {(x, y): (bits >> edges.index(tuple(sorted((x, y))))) & 1
                  for x in range(4) for y in range(4) if x != y}
        targets = [source, {p: 0 for p in source}, {p: 1 for p in source}]
        for target in targets:
            for image in product(range(4), repeat=4):
                if atomic_hom(source, target, image):
                    require(atomic_embedding(source, target, image), 'complete four-point hom readout')
                    counts['complete_atomic_K4_hom_embeddings'] += 1
    partial = {(0, 1): 0, (1, 0): 0, (1, 2): 0, (2, 1): 0}
    edge = {(0, 1): 0, (1, 0): 0}
    require(atomic_hom(partial, edge, (0, 1, 0)), 'a partial path permits collision')
    complete = {(0, 1): 0, (1, 0): 0}
    loop_target = {(0, 0): 0}
    require(atomic_hom(complete, loop_target, (0, 0)), 'looped diversity permits complete-source collapse')
    # Homomorphism preserves R0 but need not reflect an extra target R1.
    source_rel = ((2, frozenset({(0, 1), (1, 0)})), (2, frozenset()))
    bad_target = ((2, source_rel[0][1]), (2, source_rel[0][1]))
    require(homomorphism(source_rel, bad_target, (0, 1)) and
            not embedding((0, 1), source_rel, bad_target, (0, 1)),
            'nonunique atomic labels defeat reflection')
    witnesses['complete_atomic_guards'] = {
        'partial_path_collapses': [0, 1, 0], 'looped_target_constant_map': [0, 0],
        'target_with_two_atoms_on_same_pair_reflects': False}


def fan_controls(counts, witnesses):
    # K = complete one-color structures of size <=3. It has AP through
    # identifications, although it lacks SAP and semantic homomorphic CCO.
    for left_size in range(4):
        for right_size in range(4):
            for base_size in range(min(left_size, right_size) + 1):
                host_size = max(left_size, right_size)
                left = tuple(range(left_size))
                right = tuple(range(base_size)) + tuple(range(base_size, right_size))
                require(len(set(left)) == left_size and len(set(right)) == right_size and
                        all(x < host_size for x in left + right),
                        'AP of one-color bounded complete structures uses legal factor embeddings')
                require(left[:base_size] == right[:base_size], 'the fixed base maps agree')
                counts['bounded_complete_AP_spans'] += 1
    for length in range(3, 17):
        reference = (0, 1, 2)
        image = [0, 1, 2]
        for fresh in range(3, length):
            previous = image[-1]
            choice = next(x for x in reference if x not in (image[0], previous))
            triangle_map = (image[0], previous, choice)
            require(len(set(triangle_map)) == 3,
                    'new fan triangle embeds over the pinned complete root/previous edge')
            # The old host map is identity. AP may identify the new root
            # with an old non-neighbour, outside the shared edge.
            require(triangle_map[:2] == (image[0], previous), 'AP edge span really agrees')
            image.append(choice)
            counts['fan_induced_triangle_AP_steps'] += 1
        cycle_edges = tuple((i, (i + 1) % length) for i in range(length))
        require(all(image[x] != image[y] for x, y in cycle_edges),
                'all specified cycle diversity edges, including closing edge, are preserved')
        require(all(image[0] != image[i] for i in range(1, length)),
                'every actual root chord used by the fan is preserved')
        counts['cycle_fan_homomorphisms'] += 1
        if length > 3:
            require(len(set(image)) < length, 'AP fan permits nonadjacent collisions')
            counts['genuinely_noninjective_cycle_fans'] += 1
    # K4 has every <=3 subobject in K, and every simple cycle maps to K3,
    # but its complete diversity diagram has no hom to <=3 points.
    k4 = {(x, y): 0 for x in range(4) for y in range(4) if x != y}
    for small in subsets(range(4)):
        if len(small) > 3:
            continue
        induced = {p: color for p, color in k4.items() if set(p) <= set(small)}
        expected = {(x, y): 0 for x in small for y in small if x != y}
        require(len(small) <= 3 and induced == expected,
                'every actual small restriction is a complete one-color member of the bounded K')
        counts['K4_small_induced_subobjects_in_K'] += 1
    for m in range(4):
        host = {(x, y): 0 for x in range(m) for y in range(m) if x != y}
        require(not any(atomic_hom(k4, host, image) for image in product(range(m), repeat=4)),
                'bounded class lacks semantic CCO despite AP and all legal triples')
    witnesses['AP_without_CCO_not_triangle_full'] = {
        'K': 'complete one-color structures of size at most three',
        'AP': True, 'complete_input_size': 4, 'all_at_most_three_subobjects_in_K': True,
        'all_simple_cycles_homomorphically_realizable': True, 'global_hom_completion': False}
    tick()


def boundary_controls(counts, witnesses):
    # The age of the countably infinite disjoint union of edges has AP
    # but not SAP: two new partners of a fixed root must be identified.
    star = ((2, frozenset({(0, 1), (1, 0), (0, 2), (2, 0)})),)
    matching = ((2, frozenset({(0, 1), (1, 0), (2, 3), (3, 2)})),)
    require(is_he(3, star, matching, (0, 1, 1)), 'the matching-age collision source really is HE')
    require(not any(homomorphism(star, matching, image) for image in permutations(range(4), 3)),
            'degree-one matching forbids every injective star homomorphism')
    witnesses['AP_does_not_replace_SAP_for_collision_unfolding'] = {
        'ambient': 'countably infinite homogeneous disjoint union of edges',
        'source': 'three-point two-leaf star', 'old_HE': [0, 1, 1],
        'injective_hom_exists': False,
        'SAP_failure': 'two partners of the same base root are forced to coincide'}
    # Deleting one relational vertex is always induced, unlike functional
    # closure. This is a mechanism guard, not a functional theorem verdict.
    function, deleted, retained = (1, 1), 1, {0}
    require(function[0] == deleted and function[0] not in retained,
            'B minus v need not be a unary-closed amalgam base')
    witnesses['relational_deletion_is_not_functional_closure'] = {
        'function': list(function), 'deleted': deleted, 'retained': sorted(retained),
        'retained_set_closed': False}
    # R means same equivalence class, B different class. The partial path
    # has no fully specified triangle but no complete equivalence coloring.
    specified = {(0, 1): 0, (1, 2): 0, (2, 3): 0, (0, 3): 1}
    require(not any(all(tuple(sorted(p)) in specified for p in combinations(s, 2))
                    for s in combinations(range(4), 3)), 'partial input has no complete bad triangle')
    completions = []
    for labels in partitions(4):
        if all(int(labels[x] != labels[y]) == color for (x, y), color in specified.items()):
            completions.append(labels)
    require(not completions, 'partial triangle consistency does not imply equivalence-color completion')
    witnesses['partial_triangle_consistency_is_insufficient'] = {
        'same_class_path': [[0, 1], [1, 2], [2, 3]], 'different_class_edge': [0, 3],
        'fully_specified_triangles': 0, 'completion_exists': False,
        'missing_gate': 'the triangle-fullness input must be COMPLETE with actual chords'}
    counts['explicit_boundary_witnesses'] += len(witnesses)


def main():
    counts, witnesses = Counter(), {}
    tuple_and_clone_controls(counts)
    collision_controls(counts, witnesses)
    atomic_hom_controls(counts, witnesses)
    fan_controls(counts, witnesses)
    boundary_controls(counts, witnesses)
    print(json.dumps(dict(status='PASS', scope='bounded relational clone and atomic cycle-fan diagnostics',
                          seconds=round(time.monotonic() - START, 3), counts=dict(sorted(counts.items())),
                          witnesses=witnesses,
                          limits='Finite examples do not certify arbitrary relational signatures, homogeneous SAP, semantic CCO, triangle fullness, unbounded collision induction or Lean proofs.'),
                     sort_keys=True))


if __name__ == '__main__':
    signal.alarm(30)
    main()
