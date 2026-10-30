#!/usr/bin/env python3
"""Bounded B041 diagnostics for actual simultaneous typed quotients.

Finite XOR clone structures supply explicit old atomic relations, words,
nonempty exact meets, independent quotient kernels and actual class maps.
Private formal paths are checked combinatorially, not by a presumed CCO
criterion. Entire finite named-axis groups and pointwise owner kernels
are deliberately distinguished. No infinite homogeneous/CCO/SAP theorem,
arbitrary exact descent, group section or Lean proof is certified.
Reproduce: timeout 10s python tools/check_simultaneous_quotients_controls.py
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


def compose(r, s):
    outgoing = {}
    for y, z in s:
        outgoing.setdefault(y, set()).add(z)
    return frozenset((x, z) for x, y in r for z in outgoing.get(y, ()))


def classes(xs, e):
    return tuple(sorted({frozenset(y for y in xs if (x, y) in e) for x in xs}, key=repr))


def quotient_map(xs, e):
    blocks = classes(xs, e)
    return blocks, {x: block for block in blocks for x in block}


def image(relation, left, right):
    return frozenset((left[x], right[y]) for x, y in relation)


def pullback(relation, left, right):
    return frozenset((x, y) for x in left for y in right if (left[x], right[y]) in relation)


def xor_source(phases, width):
    carriers = tuple(tuple((s, p, c) for p in range(phases) for c in range(width)) for s in range(3))
    atoms = {}
    kernels = {}
    for s in range(3):
        kernels[s, 0] = identity(carriers[s])
        kernels[s, 1] = frozenset((x, y) for x, y in product(carriers[s], repeat=2) if x[1] == y[1])
        kernels[s, 2] = frozenset(product(carriers[s], repeat=2))
        for t in range(3):
            cells = {}
            for x, y in product(carriers[s], carriers[t]):
                key = ('id',) if x == y else ('difference', x[1] ^ y[1])
                cells.setdefault(key, set()).add((x, y))
            atoms[s, t] = tuple(frozenset(cell) for cell in cells.values())
    return carriers, atoms, kernels


def word_and_exact_families(carriers, atoms):
    words = {pair: set(cells) for pair, cells in atoms.items()}
    for s in range(3):
        words[s, s].add(identity(carriers[s]))
    changed = True
    while changed:
        changed = False
        for s, t, u in product(range(3), repeat=3):
            for r, a in product(tuple(words[s, t]), atoms[t, u]):
                word = compose(r, a)
                if word and word not in words[s, u]:
                    words[s, u].add(word)
                    changed = True
    exact = {}
    for (s, t), profiles in words.items():
        family = set(profiles) | {frozenset(product(carriers[s], carriers[t]))}
        changed = True
        while changed:
            changed = False
            for r, q in product(tuple(family), repeat=2):
                meet = r & q
                if meet and meet not in family:
                    family.add(meet)
                    changed = True
        exact[s, t] = family
    return words, exact


def quotient_data(carriers, atoms, kernels, levels):
    objects, maps = zip(*(quotient_map(carriers[s], kernels[s, levels[s]]) for s in range(3)))
    quotient_atoms = {pair: tuple(set(image(atom, maps[pair[0]], maps[pair[1]]) for atom in cells))
                      for pair, cells in atoms.items()}
    return objects, maps, quotient_atoms


def diversity_rank(objects, atoms):
    # Cross-sort converse pairs are counted once, same-sort equality omitted.
    return sum(len(atoms[s, t]) - (s == t) for s in range(3) for t in range(s, 3))


def menus(cells):
    if len(cells) <= 4:
        return tuple(frozenset().union(*(cells[i] for i in range(len(cells)) if mask >> i & 1))
                     for mask in range(1, 1 << len(cells)))
    return tuple(cells) + (frozenset().union(*cells),)


def single_sort_exact_family(xs, atoms):
    words = set(atoms) | {identity(xs)}
    changed = True
    while changed:
        changed = False
        for r, a in product(tuple(words), atoms):
            word = compose(r, a)
            if word and word not in words:
                words.add(word)
                changed = True
    exact = words | {frozenset(product(xs, repeat=2))}
    changed = True
    while changed:
        changed = False
        for r, q in product(tuple(exact), repeat=2):
            meet = r & q
            if meet and meet not in exact:
                exact.add(meet)
                changed = True
    return exact


def simultaneous_quotient_controls(counts, witnesses):
    for phases, width in ((2, 2), (4, 2)):
        carriers, atoms, kernels = xor_source(phases, width)
        words, exact = word_and_exact_families(carriers, atoms)
        for s in range(3):
            require(all(kernels[s, level] in exact[s, s] for level in range(3)),
                    'all chosen Id/phase/top kernels have actual old full-exact presentations')
        # The safe CONVERSE descent is checked only in a symmetric single
        # original sort, never inferred for independent mixed-sort kernels.
        xs = carriers[0]
        single_exact = single_sort_exact_family(xs, atoms[0, 0])
        for level in range(3):
            e = kernels[0, level]
            require(e in single_exact, 'single-sort chosen kernel is genuinely full exact')
            quotient, qmap = quotient_map(xs, e)
            quotient_atoms = tuple(set(image(a, qmap, qmap) for a in atoms[0, 0]))
            quotient_exact = single_sort_exact_family(quotient, quotient_atoms)
            for d in single_exact:
                if compose(compose(e, d), e) == d:
                    require(image(d, qmap, qmap) in quotient_exact,
                            'one-original-symmetric-sort exact bisaturated D descends as an actual quotient exact menu')
                    counts['one_original_sort_exact_descent_checks'] += 1
        counts['explicit_old_atomic_word_profiles'] += sum(map(len, words.values()))
        counts['explicit_nonempty_exact_menus'] += sum(map(len, exact.values()))
        data = {}
        for levels in product(range(3), repeat=3):
            objects, maps, qatoms = quotient_data(carriers, atoms, kernels, levels)
            data[levels] = objects, maps, qatoms
            for s, t in product(range(3), repeat=2):
                cells = qatoms[s, t]
                require(frozenset().union(*cells) == frozenset(product(objects[s], objects[t]))
                        and all(not (a & b) for a, b in combinations(cells, 2)),
                        'actual quotient orbital images form a complete disjoint typed palette')
                for old_atom in atoms[s, t]:
                    qatom = image(old_atom, maps[s], maps[t])
                    old_block = pullback(qatom, maps[s], maps[t])
                    require(old_block == compose(compose(kernels[s, levels[s]], old_atom), kernels[t, levels[t]]),
                            'full quotient orbital pullback is actual endpoint kernel saturation')
                    require(old_block in exact[s, t], 'sample quotient atomic block has old exact presentation')
                    counts['actual_full_exact_orbital_block_checks'] += 1
            for s, t, u in ((0, 1, 2), (0, 0, 1), (0, 1, 0)):
                for r, q in product(menus(qatoms[s, t]), menus(qatoms[t, u])):
                    old_r, old_q = pullback(r, maps[s], maps[t]), pullback(q, maps[t], maps[u])
                    actual = pullback(compose(r, q), maps[s], maps[u])
                    require(actual == compose(compose(old_r, kernels[t, levels[t]]), old_q)
                            == compose(old_r, old_q),
                            'actual quotient products equal saturated old products, including different middle representatives')
                    counts['saturated_quotient_product_checks'] += 1
            counts['independent_simultaneous_quotient_models'] += 1
        for first in data:
            objects, maps, qatoms = data[first]
            for final in product(*(range(level, 3) for level in first)):
                target, target_maps, target_atoms = data[final]
                second_maps, flatten = [], []
                for s in range(3):
                    induced_kernel = frozenset((x, y) for x, y in product(objects[s], repeat=2)
                                               if (next(iter(x)), next(iter(y))) in kernels[s, final[s]])
                    twice, second = quotient_map(objects[s], induced_kernel)
                    flat = {block: frozenset().union(*block) for block in twice}
                    require(set(flat.values()) == set(target[s]) and len(flat) == len(set(flat.values())),
                            'nested actual classes flatten canonically to direct total-kernel classes')
                    require(all(flat[second[maps[s][x]]] == target_maps[s][x] for x in carriers[s]),
                            'canonical class flattening commutes with the original real quotient maps')
                    second_maps.append(second)
                    flatten.append(flat)
                for s, t in product(range(3), repeat=2):
                    twice_atoms = {image(a, second_maps[s], second_maps[t]) for a in qatoms[s, t]}
                    flattened = {image(a, flatten[s], flatten[t]) for a in twice_atoms}
                    require(flattened == set(target_atoms[s, t]),
                            'staged and direct quotients have the exact same atomic orbital blocks')
                    counts['canonical_tower_atom_block_checks'] += 1
                old_rank, final_rank = diversity_rank(objects, qatoms), diversity_rank(target, target_atoms)
                changed = any(kernels[s, first[s]] != kernels[s, final[s]] for s in range(3))
                require(final_rank <= old_rank and (not changed or final_rank < old_rank),
                        'nonidentity quotient kernel strictly lowers typed diversity atom rank, counted consistently')
                counts['canonical_two_stage_quotient_towers'] += 1
                counts['strict_diversity_rank_drops'] += bool(changed)
        tick()
    # Actual independent mixed-sort quotienting can enlarge a projected WORD.
    carriers, atoms, kernels = xor_source(2, 2)
    a, b, c = carriers
    zero_ab = frozenset((x, y) for x, y in product(a, b) if x[1] == y[1])
    zero_bc = frozenset((x, y) for x, y in product(b, c) if x[1] == y[1])
    objects, maps, _ = quotient_data(carriers, atoms, kernels, (0, 2, 0))
    old_word = compose(zero_ab, zero_bc)
    projected_profile = image(old_word, maps[0], maps[2])
    factorwise_product = compose(image(zero_ab, maps[0], maps[1]), image(zero_bc, maps[1], maps[2]))
    require(projected_profile < factorwise_product == frozenset(product(objects[0], objects[2])),
            'projecting old word factors independently can strictly enlarge its profile')
    require(projected_profile in set(quotient_data(carriers, atoms, kernels, (0, 2, 0))[2][0, 2]),
            'the mixed-word failure does NOT refute every exact descent: this endpoint relation is still atomic')
    witnesses['unsafe_factorwise_mixed_word_projection'] = {
        'old_profile_pairs': len(projected_profile), 'projected_factor_product_pairs': len(factorwise_product),
        'strict_enlargement': True, 'old_endpoint_profile_still_quotient_atomic': True,
        'intermediate_kernel': 'top on B; identity on A,C'}


def _partitions(xs):
    if not xs:
        yield ()
        return
    for rest in _partitions(xs[1:]):
        yield (frozenset({xs[0]}),) + rest
        for i in range(len(rest)):
            yield rest[:i] + (rest[i] | {xs[0]},) + rest[i + 1:]


def finite_axis_controls(counts, witnesses):
    axes = tuple((s, p) for s in range(3) for p in range(2))
    for partition in _partitions((0, 1, 2)):
        component = {s: i for i, block in enumerate(partition) for s in block}

        def colour(x, y):
            if x[0] == y[0]:
                return (x[0], y[0], 'equal' if x == y else 'different')
            return (x[0], y[0], x[1] ^ y[1] if component[x[0]] == component[y[0]] else 'independent')

        def action(bits, x):
            return x[0], x[1] ^ bits[x[0]]

        full = tuple(bits for bits in product(range(2), repeat=3)
                     if all(colour(action(bits, x), action(bits, y)) == colour(x, y)
                            for x, y in product(axes, repeat=2)))
        require(len(full) == 2 ** len(partition), 'full binary automorphism group is computed, not assumed')
        pair_images = {(i, j): {(g[i], g[j]) for g in full} for i, j in combinations(range(3), 2)}
        for subset_size in range(4):
            for subset in combinations(range(3), subset_size):
                actual = {tuple(g[i] for i in subset) for g in full}
                compatible = {values for values in product(range(2), repeat=subset_size)
                              if all((values[i], values[j]) in pair_images[subset[i], subset[j]]
                                     for i, j in combinations(range(subset_size), 2))}
                require(actual == compatible, 'full finite named-axis group is exactly its pair constraints')
                counts['entire_finite_axis_projection_checks'] += 1
        # Check homogeneous extension of every finite sort-preserving partial map.
        charts = []
        for s in range(3):
            charts.append(({},) + tuple({(s, p): (s, q)} for p, q in product(range(2), repeat=2))
                          + tuple({(s, p): (s, p ^ shift) for p in range(2)} for shift in range(2)))
        for request in product(*charts):
            merged = {x: y for chart in request for x, y in chart.items()}
            if all(colour(x, y) == colour(merged[x], merged[y]) for x, y in product(merged, repeat=2)):
                require(any(all(action(g, x) == y for x, y in merged.items()) for g in full),
                        'every actual finite binary partial isomorphism extends in the positive whole-sort model')
                counts['actual_finite_homogeneous_axis_extensions'] += 1
        counts['entire_finite_named_axis_models'] += 1
    # Pairwise projections of an arbitrary earlier subgroup do not determine it.
    old = tuple(g for g in product(range(2), repeat=3) if sum(g) % 2 == 0)
    full = tuple(product(range(2), repeat=3))
    require(all({(g[i], g[j]) for g in old} == set(product(range(2), repeat=2))
                for i, j in combinations(range(3), 2)) and len(old) < len(full),
            'proper earlier subgroup can share every binary projection with a larger full binary automorphism group')
    witnesses['full_binary_group_is_not_an_arbitrary_earlier_subgroup'] = {
        'earlier_even_parity_subgroup_size': len(old), 'full_named_binary_group_size': len(full),
        'all_pair_projections_equal': True,
        'scope': 'outside a claim of full homogeneous old-source action; guards against substituting an arbitrary subgroup'}
    # Actual fine two-sort phase group is diagonal C2; coarsen U to singleton.
    fine = ((0, 0), (1, 1))
    coarse_images = {g: (0, g[1]) for g in fine}
    owner_kernel = tuple(g for g in fine if coarse_images[g] == (0, 0))
    require(owner_kernel == ((0, 0),) and {g[0] for g in owner_kernel} == {0},
            'pointwise coarse-owner kernel is trivial despite intrinsic two-point U fibre symmetry')
    witnesses['pointwise_owner_kernel_is_not_intrinsic_fibre_group'] = {
        'full_fine_diagonal_group_size': len(fine), 'pointwise_coarse_kernel_size': len(owner_kernel),
        'intrinsic_U_fibre_group_size': 2,
        'not_a_counterexample_to_entire_named_axis_projection': True}
    tick()



def _pc_contract_word(word):
    """Actually quotient the linear formal path by its equality edges."""
    parent = list(range(len(word) + 1))

    def find(x):
        while parent[x] != x:
            parent[x] = parent[parent[x]]
            x = parent[x]
        return x

    for i, colour in enumerate(word):
        if colour == 'eq':
            parent[find(i + 1)] = find(i)
    if find(0) == find(len(word)):
        raise ValueError('zero diversity length would identify distinct marked endpoints')
    edges = [(find(i), find(i + 1), colour) for i, colour in enumerate(word) if colour != 'eq']
    if any(a == b for a, b, _ in edges):
        raise AssertionError('a non-equality edge became a loop')
    if any(edges[i][1] != edges[i + 1][0] for i in range(len(edges) - 1)):
        raise AssertionError('contracted word is not a linear path')
    return tuple(colour for _, _, colour in edges)


def _pc_cycles(adjacency):
    """Enumerate each undirected simple cycle once, no invented 2-cycles."""
    for start in sorted(adjacency):
        stack = [(start, (start,))]
        while stack:
            last, path = stack.pop()
            for following in adjacency[last]:
                if following == start:
                    if len(path) >= 3 and path[1] < path[-1]:
                        yield path
                elif following > start and following not in path:
                    stack.append((following, path + (following,)))


def _pc_graph(n, base, configurations, counts):
    adjacency = {v: set() for v in range(n)}
    edge_paths = {}
    paths = {}
    direct_colours = {}
    next_vertex = n
    next_path = 0
    for edge_number, (u, v) in enumerate(base):
        for word in configurations[edge_number]:
            contracted = _pc_contract_word(word)
            counts['path_word_equality_contractions'] += word.count('eq')
            if len(contracted) == 1 and (u, v) in direct_colours:
                if direct_colours[u, v] != contracted[0]:
                    raise ValueError('inconsistent coincident length-one atomic colours')
                counts['coincident_length_one_paths_merged'] += 1
                continue
            if len(contracted) == 1:
                direct_colours[u, v] = contracted[0]
            vertices = (u,) + tuple(range(next_vertex, next_vertex + len(contracted) - 1)) + (v,)
            next_vertex += len(contracted) - 1
            pid = next_path
            next_path += 1
            paths[pid] = ((u, v), vertices)
            for x, y in zip(vertices, vertices[1:]):
                adjacency.setdefault(x, set()).add(y)
                adjacency.setdefault(y, set()).add(x)
                key = frozenset((x, y))
                if key in edge_paths:
                    raise AssertionError('positive construction has nonprivate path edges')
                edge_paths[key] = pid
    for vertex, neighbours in adjacency.items():
        if vertex >= n:
            require(len(neighbours) == 2, 'every private internal vertex has specified degree two')
    return adjacency, edge_paths, paths


def private_cycle_controls(counts, witnesses):
    from itertools import combinations, product
    patterns = (
        (('d',),),
        (('eq', 'd', 'eq'), ('d',)),
        (('d', 'd'), ('d', 'd', 'd')),
        (('d',), ('d', 'd'), ('eq', 'd', 'd', 'd', 'eq')),
        (('eq', 'd', 'eq', 'd'), ('d', 'eq', 'd')),
    )
    for n in (2, 3, 4):
        possible = tuple(combinations(range(n), 2))
        for mask in range(1 << len(possible)):
            base = tuple(edge for i, edge in enumerate(possible) if mask >> i & 1)
            # Every simple base graph is used, with five uniform and one
            # mixed multi-path decoration; no combinatorial model cutoff.
            configurations = [tuple(pattern for _ in base) for pattern in patterns]
            configurations.append(tuple(patterns[i % len(patterns)] for i in range(len(base))))
            for config in configurations:
                adjacency, edge_paths, paths = _pc_graph(n, base, config, counts)
                for cycle in _pc_cycles(adjacency):
                    marked = [i for i, v in enumerate(cycle) if v < n]
                    require(len(marked) >= 2, 'a raw simple cycle cannot avoid all but one marked root')
                    used_paths = []
                    for pos, start in enumerate(marked):
                        finish = marked[(pos + 1) % len(marked)]
                        arc = [cycle[start]]
                        j = (start + 1) % len(cycle)
                        while j != finish:
                            arc.append(cycle[j])
                            j = (j + 1) % len(cycle)
                        arc.append(cycle[finish])
                        pids = {edge_paths[frozenset((x, y))] for x, y in zip(arc, arc[1:])}
                        require(len(pids) == 1, 'a cycle arc between marked roots traverses ONE whole private path')
                        pid = next(iter(pids))
                        original = paths[pid][1]
                        require(tuple(arc) in (original, tuple(reversed(original))),
                                'a cycle cannot enter/leave an internal private path early')
                        used_paths.append(pid)
                    if len(marked) == 2:
                        require(len(set(used_paths)) == 2 and
                                paths[used_paths[0]][0] == paths[used_paths[1]][0],
                                'two-marked cycle uses two different paths above ONE base edge')
                        counts['two_private_paths_one_edge_cycles'] += 1
                    else:
                        roots = [cycle[i] for i in marked]
                        require(len(set(roots)) == len(roots) and all(
                            tuple(sorted((x, y))) in base
                            for x, y in zip(roots, roots[1:] + roots[:1])),
                            'three-plus marked roots project to a SIMPLE specified base cycle')
                        counts['projected_simple_base_cycles'] += 1
                    counts['raw_private_simple_cycles'] += 1
                counts['private_path_expansion_models'] += 1
                tick()

    # Sharing an internal point between two paths permits a raw cycle
    # having only ONE marked point, outside the lemma's private premise.
    adjacency = {v: set() for v in range(6)}
    for path in ((0, 3, 5, 1), (0, 4, 5, 2)):
        for x, y in zip(path, path[1:]):
            adjacency[x].add(y)
            adjacency[y].add(x)
    bad = tuple(c for c in _pc_cycles(adjacency) if sum(v < 3 for v in c) == 1)
    require(bad, 'nonprivate internals can create cycles with only one marked root')
    witnesses['nonprivate_internal_vertex_boundary'] = {
        'raw_cycle': list(bad[0]), 'marked_roots_on_cycle': 1,
        'shared_internal_degree': len(adjacency[5])}
    for word in ((), ('eq',), ('eq', 'eq')):
        try:
            _pc_contract_word(word)
        except ValueError:
            counts['zero_length_path_guards'] += 1
        else:
            raise AssertionError('a zero-length path was silently admitted')
    try:
        _pc_graph(2, ((0, 1),), ((('a',), ('b',)),), counts)
    except ValueError:
        counts['inconsistent_parallel_atomic_guards'] += 1
    else:
        raise AssertionError('inconsistent coincident atomic paths were admitted')
    witnesses['zero_and_inconsistent_path_boundaries'] = {
        'zero_diversity_length_rejected': True,
        'inconsistent_coincident_length_one_colours_rejected': True,
        'merged_length_one_edge_is_not_a_two_cycle': True}


def main():
    counts, witnesses = Counter(), {}
    private_cycle_controls(counts, witnesses)
    simultaneous_quotient_controls(counts, witnesses)
    finite_axis_controls(counts, witnesses)
    print(json.dumps(dict(status='PASS', seconds=round(time.monotonic() - START, 3),
        scope='bounded private-path, actual independent quotient/tower and entire-finite-axis diagnostics',
        counts=dict(sorted(counts.items())), witnesses=witnesses,
        limits='Finite diagnostics only: no general homogeneous/CCO/SAP theorem, unrestricted exact descent, global automorphism lift/section or Lean proof is certified.'), sort_keys=True))


if __name__ == '__main__':
    signal.alarm(30)
    main()
