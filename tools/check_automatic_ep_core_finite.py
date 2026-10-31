#!/usr/bin/env python3
"""Independent bounded actual-table tests for B063, not infinite certificates."""
from collections import deque
from itertools import combinations, product
import json


def compose(left, right):
    return {(x, z) for x, y in left for u, z in right if y == u}


def bipartite(points, edges):
    graph = {x: set() for x in points}
    for x, y in edges:
        graph[x].add(y)
        graph[y].add(x)
    side = {}
    for start in points:
        if start in side:
            continue
        side[start] = 0
        queue = deque([start])
        while queue:
            x = queue.popleft()
            for y in graph[x]:
                if y in side:
                    if side[y] == side[x]:
                        return False
                else:
                    side[y] = side[x] ^ 1
                    queue.append(y)
    return True


def endomorphisms(points, relations):
    """Enumerate all positive relational endomorphisms, allowing collisions."""
    points = tuple(points)
    answers = []
    partial = {}

    def search():
        if len(partial) == len(points):
            answers.append(tuple(partial[x] for x in points))
            return
        x = points[len(partial)]
        for image in points:
            partial[x] = image
            if all((partial[a], partial[b]) in relation
                   for relation in relations.values()
                   for a in partial for b in partial if (a, b) in relation):
                search()
            del partial[x]
    search()
    return answers


def support(vertices, atom, labels):
    names = {atom(x, y) for x in vertices for y in vertices if x != y}
    return {a: {(labels[x], labels[y]) for x in vertices for y in vertices
                if x != y and atom(x, y) == a} for a in names}


def regular_functional_sources():
    functional_graphs = prefix_actions = action_products = terminal_separators = 0
    total_endomorphisms = inner_prefix_cases = 0
    for dimension in range(4):
        points = tuple(range(1 << dimension))
        atom = lambda x, y: x ^ y
        table = {a: {(x, y) for x in points for y in points if x ^ y == a}
                 for a in points if a}
        actual_functions = {}
        for h in points:
            graph = {(x, y) for x in points for y in points if x ^ y == h}
            images = {x: [y for p, y in graph if p == x] for x in points}
            assert all(len(values) == 1 for values in images.values())
            f = tuple(images[x][0] for x in points)
            assert all(f[f[x]] == x for x in points)
            if h:
                assert all(f[x] != x for x in points)
                assert bipartite(points, graph)
            actual_functions[h] = f
            functional_graphs += 1
        # Composition of actual functions is independently compared with
        # the entire observed function set, including commutativity.
        for f, g in product(actual_functions.values(), repeat=2):
            fg = tuple(g[f[x]] for x in points)
            assert fg in set(actual_functions.values())
            assert fg == tuple(f[g[x]] for x in points)
        for length in range(dimension + 1):
            mask = (1 << length) - 1
            labels = {x: x & mask for x in points}
            types = set(labels.values())
            identity = {(t, t) for t in types}
            actions = {}
            for h, f in actual_functions.items():
                relation = {(labels[x], labels[f[x]]) for x in points}
                assert relation == {(y, x) for x, y in relation}
                assert compose(relation, relation) == identity
                assert all(sum(p == t for p, q in relation) == 1 for t in types)
                actions[h] = relation
                prefix_actions += 1
            for h, g in product(points, repeat=2):
                assert compose(actions[h], actions[g]) == actions[h ^ g]
                action_products += 1
            # For dimension>0 the least positive exact F is Top and H_F=H.
            # The dimension-zero base just tests the trivial singleton action.
            # The observed action is transitive on the one occupancy class.
            assert {y for h in points for x, y in actions[h] if x == 0} == types
            inner_prefix_cases += 1
            if length < dimension:
                odd = 1 << length
                f = actual_functions[odd]
                assert all(labels[f[x]] == labels[x] for x in points)
                next_mask = (1 << (length + 1)) - 1
                assert all((f[x] & next_mask) == ((x & next_mask) ^ odd) for x in points)
        for x, y in permutations_pairs(points):
            h = x ^ y
            assert h and (x, y) in table[h]
            assert all((t, t) not in table[h] for t in points)
            terminal_separators += 1
        endos = endomorphisms(points, table)
        assert len(endos) == len(points)
        assert all(len(set(f)) == len(points) for f in endos)
        assert set(endos) == set(actual_functions.values())
        total_endomorphisms += len(endos)
    return dict(functional_graphs=functional_graphs, prefix_type_actions=prefix_actions,
                observed_action_products=action_products,
                terminal_functional_separators=terminal_separators,
                regular_source_endomorphisms=total_endomorphisms,
                identity_gate_prefix_orbits=inner_prefix_cases)


def permutations_pairs(points):
    return ((x, y) for x in points for y in points if x != y)


def graph_offset_lifts():
    # Direct actual permutations of four child points, compared with the
    # equivalence relation defined by adjusted (bit + offset) occupancy.
    cases = transported = 0
    points = tuple(product(range(2), repeat=2))
    for gamma in product(range(2), repeat=2):
        adjusted = {(p, b): b ^ gamma[p] for p, b in points}
        occupancy = {(x, y) for x in points for y in points if adjusted[x] == adjusted[y]}
        actions = []
        for shift in range(2):
            f = {(p, b): (p ^ shift, b ^ gamma[p] ^ gamma[p ^ shift]) for p, b in points}
            assert all((x, f[x]) in occupancy for x in points)
            assert all(f[x][0] == (x[0] ^ shift) for x in points)
            actions.append(f)
            transported += 1
        for bit in range(2):
            child_class = {x for x in points if adjusted[x] == bit}
            assert {p for p, b in child_class} == {0, 1}
            assert len(child_class) == 2
            for x in child_class:
                assert {f[x] for f in actions} == child_class
            cases += 1
    return dict(bijective_offset_lifts=cases, offset_preserving_actions=transported)


def coordinate_source_and_negative_control():
    vertices = tuple(product(range(4), range(2), range(3)))
    seeds = {i: i // 2 for i in range(4)}

    def colour(x, y):
        if x == y:
            return 'I'
        if x[0] == y[0]:
            return 'c' if x[1] == y[1] else 'b'
        return 'r' if x[1] == y[1] else 's'

    names = ('I', 'c', 'b', 'r', 's')
    atomic = {a: {(i, j) for i, x in enumerate(vertices) for j, y in enumerate(vertices)
                  if colour(x, y) == a} for a in names}
    mul_table = {(a, b): frozenset(colour(vertices[x], vertices[z])
                                  for x, y in atomic[a] for u, z in atomic[b] if y == u)
                 for a, b in product(names, repeat=2)}

    def multiply(left, right):
        return frozenset().union(*(mul_table[a, b] for a in left for b in right))

    reachable = {frozenset([a]) for a in names}
    while True:
        extra = {multiply(a, b) for a in reachable for b in reachable} - reachable
        if not extra:
            break
        reachable |= extra
    exact = reachable | {frozenset(names)}
    while True:
        extra = {a & b for a in exact for b in exact if a & b} - exact
        if not extra:
            break
        exact |= extra
    invariant_equivalences = {frozenset(['I', *chosen])
                             for size in range(5)
                             for chosen in combinations(names[1:], size)
                             if multiply(frozenset(['I', *chosen]), frozenset(['I', *chosen]))
                             <= frozenset(['I', *chosen])}
    identity = frozenset(['I'])
    clone = frozenset(['I', 'c'])
    block = frozenset(['I', 'c', 'b'])
    sheet = frozenset(['I', 'c', 'r'])
    top = frozenset(names)
    assert invariant_equivalences == {identity, clone, block, sheet, top}
    exact_equivalences = invariant_equivalences & exact
    assert exact_equivalences == {identity, clone, sheet, top}
    complements = {e for e in exact_equivalences if clone <= e and e & block == clone}
    assert complements == {clone, sheet} and clone < sheet
    assert multiply(frozenset(['c']), frozenset(['c'])) == clone
    assert multiply(frozenset(['r']), frozenset(['r'])) == sheet

    bp = {a for a in names[1:] if bipartite(range(len(vertices)), atomic[a])}
    assert bp == {'b', 's'}
    bad_labels = {x: (x[1] ^ seeds[x[0]], x[1]) for x in vertices}
    good_labels = {x: x[1] for x in vertices}
    bad = support(vertices, colour, bad_labels)
    good = support(vertices, colour, good_labels)
    bad_types = tuple(sorted(set(bad_labels.values())))
    good_types = tuple(sorted(set(good_labels.values())))
    assert len(bad_types) == 4 and len(good_types) == 2
    bad_endos = endomorphisms(bad_types, bad)
    good_endos = endomorphisms(good_types, good)
    retract = tuple((mu, mu) for lam, mu in bad_types)
    assert retract in bad_endos and len(set(retract)) == 2
    retract_map = dict(zip(bad_types, retract))
    assert all(retract_map[retract_map[x]] == retract_map[x] for x in bad_types)
    assert all(len(set(f)) == 2 for f in good_endos) and len(good_endos) == 2
    # Original bipartite atoms have no terminal diagonal in either model,
    # but only the genuine MAXIMAL model has complete pair separation.
    for a in bp:
        assert all((t, t) not in bad[a] for t in bad_types)
        assert all((t, t) not in good[a] for t in good_types)
    missing = [(x, y) for x, y in permutations_pairs(bad_types)
               if not any((x, y) in bad[a] for a in bp)]
    assert missing and all(x[1] == y[1] for x, y in missing)
    assert all(any((x, y) in good[a] for a in bp)
               for x, y in permutations_pairs(good_types))
    # Quotient E=sheet has exactly two bit-classes. Its flip orbital is
    # bipartite and every old atom in its pullback is itself bipartite.
    quotient_flip = {(0, 1), (1, 0)}
    lifted_atoms = {a for a in names[1:] if any(
        (vertices[x][1], vertices[y][1]) in quotient_flip for x, y in atomic[a])}
    assert lifted_atoms == bp
    for a in lifted_atoms:
        assert all((vertices[x][1], vertices[y][1]) in quotient_flip for x, y in atomic[a])
    quotient_orbitals = {frozenset((vertices[x][1], vertices[y][1]) for x, y in atomic[a])
                         for a in names}
    quotient_diagonal = frozenset([(0, 0), (1, 1)])
    quotient_diversity = quotient_orbitals - {quotient_diagonal}
    assert quotient_diversity == {frozenset(quotient_flip)}
    assert len(quotient_diversity) < len(names[1:])
    assert sum(any((x[1], y[1]) == (0, 1) for x in vertices for y in vertices
                   if colour(x, y) == a) for a in lifted_atoms) == 2
    return dict(coordinate_vertices=len(vertices), actual_old_atoms=4,
                full_invariant_equivalences=len(invariant_equivalences),
                represented_exact_equivalences=len(exact_equivalences),
                candidate_complements=len(complements),
                bad_terminal_types=len(bad_types), bad_table_endomorphisms=len(bad_endos),
                proper_retraction_image=len(set(retract)),
                maximal_table_endomorphisms=len(good_endos),
                nonmaximal_unseparated_ordered_pairs=len(missing),
                actual_quotient_diversity_rank=len(quotient_diversity),
                original_bipartite_pullbacks=len(lifted_atoms))


def main():
    result = {}
    result.update(regular_functional_sources())
    result.update(graph_offset_lifts())
    result.update(coordinate_source_and_negative_control())
    result['status'] = 'PASS_BOUNDED_DIAGNOSTICS_ONLY'
    print(json.dumps(result, sort_keys=True))


if __name__ == '__main__':
    main()
