#!/usr/bin/env python3
"""Bounded B042 diagnostics for finite real fibres and atom graphs.

All relations, automorphisms, group tables, subgroups and fibre orbits
below are computed on actual finite sets. These checks do not prove the
unbounded high-girth/high-chromatic theorem, general semantic CCO, general
finite-group theorems, imaginary inheritance or a Lean implementation.
The Mycielski(C5) example is one finite obstruction for K3, not a general
Erdos construction. The sampled homogeneous fibre models are tested on
their actual full automorphism groups, never a presumed earlier action.
Reproduce: timeout 10s python tools/check_finite_fibres_controls.py
"""
from collections import Counter, deque
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


def subsets(xs):
    xs = tuple(xs)
    for size in range(len(xs) + 1):
        yield from combinations(xs, size)


def cycle_walk(r, m):
    """A closed m-edge walk in the simple odd cycle C_r."""
    if m % 2 == 0:
        return tuple(i % 2 for i in range(m + 1))
    require(m >= r and (m - r) % 2 == 0, 'odd walk has enough length')
    result = [0]
    for _ in range((m - r) // 2):
        result.extend((1, 0))
    result.extend(i % r for i in range(1, r + 1))
    return tuple(result)


def colouring(adjacency, bound):
    """Return an actual proper colouring, or exhaust all choices."""
    vertices = tuple(sorted(adjacency, key=lambda x: -len(adjacency[x])))
    assigned = {}

    def search(i):
        if i == len(vertices):
            return dict(assigned)
        x = vertices[i]
        forbidden = {assigned[y] for y in adjacency[x] if y in assigned}
        for colour in range(bound):
            if colour not in forbidden:
                assigned[x] = colour
                result = search(i + 1)
                if result is not None:
                    return result
                del assigned[x]
        return None

    return search(0)


def graph_walk_controls(counts, witnesses):
    for r in (3, 5, 7, 9, 11):
        for m in range(3, 36):
            if m % 2 and m < r:
                continue
            walk = cycle_walk(r, m)
            require(len(walk) == m + 1 and walk[0] == walk[-1], 'walk closes at prescribed length')
            require(all((x - y) % r in (1, r - 1) for x, y in zip(walk, walk[1:])),
                    'even fold and odd backtracks preserve every irreflexive atom edge')
            counts['even_fold_or_odd_backtrack_walks'] += 1
    # Every map to a loopless graph is a proper vertex colouring, whether
    # or not it is injective or reflects absent edges.
    for n in range(5):
        pairs = tuple(combinations(range(n), 2))
        for mask in range(1 << len(pairs)):
            edges = tuple(pair for bit, pair in enumerate(pairs) if mask >> bit & 1)
            for target_size in (2, 3):
                for images in product(range(target_size), repeat=n):
                    is_hom = all(images[x] != images[y] for x, y in edges)
                    if is_hom:
                        classes = tuple({x for x in range(n) if images[x] == c} for c in range(target_size))
                        require(all(not ({x, y} <= block) for block in classes for x, y in edges),
                                'loopless colour-preserving homomorphism gives independent colour classes')
                        counts['proper_colouring_from_homomorphism_checks'] += 1
    # Mycielski(C5): triangle-free but not 3-colourable. Every one of its
    # simple cycles has length >=4, hence maps into K3 by the walk above.
    graph = {x: set() for x in range(11)}

    def edge(x, y):
        graph[x].add(y)
        graph[y].add(x)

    for x in range(5):
        y = (x + 1) % 5
        edge(x, y)
        edge(x, y + 5)
        edge(y, x + 5)
        edge(10, x + 5)
    require(not any(y in graph[z] for x in graph for y, z in combinations(graph[x], 2)),
            'Mycielski C5 has no triangle, hence girth greater than three')
    require(colouring(graph, 3) is None and colouring(graph, 4) is not None,
            'explicit finite obstruction has chromatic number four')
    for length in range(4, 12):
        walk = cycle_walk(3, length)
        require(all(x != y for x, y in zip(walk, walk[1:])),
                'every possible simple-cycle length in this triangle-free graph maps to K3')
    witnesses['K3_is_not_homomorphic_CCO'] = {
        'obstruction': 'Mycielski(C5)', 'vertices': 11,
        'triangle_free': True, 'chromatic_number': 4,
        'all_simple_cycles_hom_to_K3': True, 'whole_graph_hom_to_K3': False,
        'scope': 'one finite witness; not the general high-girth/high-chromatic theorem'}
    tick()


def permutation_order(g):
    n = len(g)
    image = tuple(range(n))
    for k in range(1, 121):
        image = tuple(g[image[x]] for x in range(n))
        if image == tuple(range(n)):
            return k
    raise AssertionError('small permutation order search exhausted')


def odd_prime_automorphism_controls(counts):
    for n in range(1, 6):
        pairs = tuple(combinations(range(n), 2))
        perms = tuple(permutations(range(n)))
        orders = {g: permutation_order(g) for g in perms}
        for mask in range(1 << len(pairs)):
            colours = {pair: mask >> bit & 1 for bit, pair in enumerate(pairs)}

            def col(x, y):
                return -1 if x == y else colours[tuple(sorted((x, y)))]

            group = tuple(g for g in perms if all(col(g[x], g[y]) == col(x, y) for x, y in pairs))
            if all(bipartition(n, (pair for pair in pairs if colours[pair] == atom)) is not None
                   for atom in (0, 1)):
                require(len(group) & (len(group) - 1) == 0,
                        'bipartite diversity atom graphs force a power-of-two full group in the exhaustive sample')
                counts['bipartite_atom_group_order_checks'] += 1
            for g in group:
                p = orders[g]
                if p not in (3, 5):
                    continue
                x = next(x for x in range(n) if g[x] != x)
                orbit = [x]
                for _ in range(p - 1):
                    orbit.append(g[orbit[-1]])
                require(len(set(orbit)) == p and g[orbit[-1]] == x,
                        'a moved point of a prime-order permutation has the full prime orbit')
                atom = col(x, g[x])
                require(all(col(y, g[y]) == atom for y in orbit),
                        'successive prime orbit edges form a monochromatic odd simple cycle')
                counts['odd_prime_monochromatic_orbit_checks'] += 1
            counts['finite_symmetric_atomic_automorphism_models'] += 1
        tick()


def cyclic(n):
    return 'C' + str(n), tuple(tuple((a + b) % n for b in range(n)) for a in range(n))


def elementary(d):
    n = 1 << d
    return 'F2^' + str(d), tuple(tuple(a ^ b for b in range(n)) for a in range(n))


def dihedral_eight():
    return 'D8', tuple(tuple(((a % 4 + (-1 if a // 4 else 1) * (b % 4)) % 4)
                            + 4 * ((a // 4) ^ (b // 4)) for b in range(8)) for a in range(8))


def quaternion_eight():
    # i*j=k, j*k=i, k*i=j; reverse products have negative sign.
    units = (((0, 0), (1, 0), (2, 0), (3, 0)),
             ((1, 0), (0, 1), (3, 0), (2, 1)),
             ((2, 0), (3, 1), (0, 1), (1, 0)),
             ((3, 0), (2, 0), (1, 1), (0, 1)))
    return 'Q8', tuple(tuple(units[a % 4][b % 4][0]
                            + 4 * (units[a % 4][b % 4][1] ^ (a // 4) ^ (b // 4))
                            for b in range(8)) for a in range(8))


def symmetric_three():
    elements = (tuple(range(3)),) + tuple(g for g in permutations(range(3)) if g != tuple(range(3)))
    index = {g: i for i, g in enumerate(elements)}
    return 'S3', tuple(tuple(index[tuple(a[b[i]] for i in range(3))] for b in elements) for a in elements)


def inverse_table(table):
    n = len(table)
    require(all(table[0][a] == table[a][0] == a for a in range(n)), 'group table identity is zero')
    require(all(table[table[a][b]][c] == table[a][table[b][c]]
                for a, b, c in product(range(n), repeat=3)), 'actual table is associative')
    return tuple(next(b for b in range(n) if table[a][b] == table[b][a] == 0) for a in range(n))


def subgroups(table):
    n = len(table)
    return tuple(frozenset({0, *rest}) for rest in subsets(range(1, n))
                 if all(table[a][b] in {0, *rest} for a in (0, *rest) for b in (0, *rest)))


def cauchy_controls(counts):
    for name, table in (cyclic(3), cyclic(5), cyclic(6), symmetric_three()):
        n = len(table)
        inverses = inverse_table(table)
        for p in (3, 5):
            if n % p:
                continue
            tuples = set()
            for initial in product(range(n), repeat=p - 1):
                value = 0
                for x in initial:
                    value = table[value][x]
                tuples.add(initial + (inverses[value],))
            require(len(tuples) == n ** (p - 1), 'product-one tuples counted by their free first p-minus-one entries')
            require(all(t[1:] + t[:1] in tuples for t in tuples), 'cyclic rotation preserves product-one condition')
            fixed = tuple(t for t in tuples if t[1:] + t[:1] == t)
            require(len(fixed) % p == len(tuples) % p == 0 and len(fixed) >= p,
                    'rotation fixed-point congruence forces nonidentity p-torsion')
            require(any(t[0] != 0 for t in fixed), 'identity tuple is not the only rotation fixed point')
            for t in tuples:
                orbit = {t[i:] + t[:i] for i in range(p)}
                require(len(orbit) in (1, p), 'prime rotation orbits have size one or p')
                counts['cauchy_rotation_tuple_checks'] += 1
            counts['cauchy_finite_group_instances'] += 1
        tick()


def group_correspondence_controls(counts, witnesses):
    models = (cyclic(1), cyclic(2), cyclic(4), cyclic(8), elementary(2), elementary(3),
              dihedral_eight(), quaternion_eight())
    for name, table in models:
        n = len(table)
        inverses = inverse_table(table)
        groups = subgroups(table)
        centre = {a for a in range(n) if all(table[a][b] == table[b][a] for b in range(n))}
        require(n == 1 or len(centre) >= 2, 'nontrivial finite 2-group has nontrivial centre in the sample')
        for h in groups:
            if len(h) < n:
                normalizer = {g for g in range(n)
                              if {table[table[g][x]][inverses[g]] for x in h} == h}
                require(h < normalizer, 'proper subgroup of a finite 2-group is strictly below its normalizer')
                if not any(h < k and len(k) < n for k in groups):
                    require(len(h) * 2 == n and len(normalizer) == n,
                            'maximal proper subgroup is normal and has index two')
                counts['pgroup_normalizer_checks'] += 1
        for stabilizer in groups:
            cosets = tuple(sorted({frozenset(table[g][h] for h in stabilizer) for g in range(n)}, key=repr))
            representatives = {coset: min(coset) for coset in cosets}
            base = next(coset for coset in cosets if 0 in coset)
            actions = tuple({coset: frozenset(table[g][h] for h in coset) for coset in cosets} for g in range(n))
            interval = tuple(h for h in groups if stabilizer <= h)
            relations = {}
            for h in interval:
                relation = frozenset((a, b) for a, b in product(cosets, repeat=2)
                                     if table[inverses[representatives[a]]][representatives[b]] in h)
                require(all((a, a) in relation for a in cosets)
                        and all((b, a) in relation for a, b in relation)
                        and all((a, c) in relation for a, b in relation for bb, c in relation if b == bb),
                        'subgroup above point stabilizer gives an actual equivalence')
                require(all(frozenset((g[a], g[b]) for a, b in relation) == relation for g in actions),
                        'actual equivalence is invariant under the full supplied group action')
                back = frozenset(g for g in range(n) if (actions[g][base], base) in relation)
                require(back == h, 'equivalence-to-subgroup reconstruction recovers the original subgroup')
                relations[h] = relation
                counts['subgroup_equivalence_correspondences'] += 1
            for u, v in product(interval, repeat=2):
                require((u <= v) == (relations[u] <= relations[v]), 'subgroup interval and invariant-equivalence order agree')
                if not u < v or any(u < h < v for h in groups):
                    continue
                require(len(v) == 2 * len(u), 'all actual 2-group interval covers have subgroup index two')
                for point in cosets:
                    vclass = frozenset(y for y in cosets if (point, y) in relations[v])
                    uclasses = {frozenset(z for z in cosets if (y, z) in relations[u]) for y in vclass}
                    require(len(uclasses) == 2, 'relative equivalence-class count is uniformly the subgroup index')
                    counts['hasse_equivalence_local_index_checks'] += 1
                counts['hasse_subgroup_covers'] += 1
            kernel = {g for g in range(n) if all(actions[g][coset] == coset for coset in cosets)}
            counts['nonfaithful_coset_action_instances'] += len(kernel) > 1 and len(cosets) > 1
            counts['transitive_coset_action_instances'] += 1
        counts['finite_two_group_models'] += 1
        tick()
    # Transitivity is what makes the local class index uniform.
    u = frozenset((x, x) for x in range(3))
    v = u | {(0, 1), (1, 0)}
    swap = (1, 0, 2)
    require(frozenset((swap[x], swap[y]) for x, y in v) == v,
            'nonuniform-index boundary really uses an invariant equivalence under C2')
    actual = [len({frozenset(z for z in range(3) if (y, z) in u)
                   for y in range(3) if (x, y) in v}) for x in range(3)]
    require(actual == [2, 2, 1], 'a nontransitive C2 action has a cover with NONUNIFORM local indices')
    witnesses['nontransitive_cover_has_no_uniform_index'] = {
        'action': 'C2 swaps 0,1 and fixes 2', 'cover': 'identity < {0,1}|{2}',
        'local_class_indices': actual, 'scope': 'does not contradict the transitive theorem'}
    _, odd_table = cyclic(3)
    require(subgroups(odd_table) == (frozenset({0}), frozenset({0, 1, 2})),
            'regular C3 has exactly the identity-to-top subgroup cover of index three')
    witnesses['odd_group_outside_CCO_has_index_three'] = {
        'action': 'regular C3', 'cover': 'identity < top', 'relative_index': 3,
        'scope': 'outside the finite-2-group and symmetric HOM-CCO hypotheses'}


def full_automorphisms(n, col):
    pairs = tuple(combinations(range(n), 2))
    return tuple(g for g in permutations(range(n)) if all(col(g[x], g[y]) == col(x, y) for x, y in pairs))


def bipartition(n, edges):
    graph = {x: set() for x in range(n)}
    for x, y in edges:
        graph[x].add(y)
        graph[y].add(x)
    values = {}
    for x in range(n):
        if x in values:
            continue
        values[x] = 0
        queue = deque((x,))
        while queue:
            y = queue.popleft()
            for z in graph[y]:
                if z not in values:
                    values[z] = 1 - values[y]
                    queue.append(z)
                elif values[z] == values[y]:
                    return None
    return values


def finite_fibre_models():
    for dimension in range(4):
        n = 1 << dimension
        yield 'regular-F2^' + str(dimension), n, lambda x, y: -1 if x == y else x ^ y
    for dimension in (1, 2):
        n = 2 << dimension
        yield 'two-clone-phases-F2^' + str(dimension), n, lambda x, y: -1 if x == y else (x // 2) ^ (y // 2)
    for height in (2, 3):
        n = 1 << height
        yield 'binary-tree-height-' + str(height), n, lambda x, y: -1 if x == y else (x ^ y).bit_length()


def partitions(xs):
    if not xs:
        yield ()
        return
    for rest in partitions(xs[1:]):
        yield (frozenset({xs[0]}),) + rest
        for i in range(len(rest)):
            yield rest[:i] + (rest[i] | {xs[0]},) + rest[i + 1:]


def actual_source_hasse_controls(n, group, col, palette, counts):
    equivalences = []
    for blocks in partitions(tuple(range(n))):
        block_set = set(blocks)
        if all(frozenset(g[x] for x in block) in block_set for g in group for block in blocks):
            relation = frozenset((x, y) for block in blocks for x in block for y in block)
            equivalences.append((relation, blocks))
    for atom in palette:
        pairs = frozenset((x, y) for x, y in product(range(n), repeat=2) if col(x, y) == atom)
        x, y = next(iter(pairs))
        require(frozenset((g[x], g[y]) for g in group) == pairs,
                'each named atom is exactly one ACTUAL full-group pair orbital in the sample')
        require(all(not (relation & pairs) or pairs <= relation for relation, _ in equivalences),
                'every invariant equivalence is a union of whole named atom orbitals')
        counts['actual_named_pair_orbital_checks'] += 1
    lengths = {frozenset((x, x) for x in range(n)): 0}
    for relation, blocks in sorted(equivalences, key=lambda item: len(item[0])):
        if relation not in lengths:
            raise AssertionError('invariant lattice chain did not reach an equivalence')
        for upper, upper_blocks in equivalences:
            if not relation < upper or any(relation < middle < upper for middle, _ in equivalences):
                continue
            for vclass in upper_blocks:
                require(sum(block <= vclass for block in blocks) == 2,
                        'ACTUAL finite source invariant-equivalence Hasse cover has uniform index two')
            candidate = lengths[relation] + 1
            require(upper not in lengths or lengths[upper] == candidate,
                    'every saturated chain reaching one equivalence has the same binary-index length')
            lengths[upper] = candidate
            counts['actual_source_hasse_covers'] += 1
    top = frozenset(product(range(n), repeat=2))
    require(2 ** lengths[top] == n and lengths[top] <= len(palette),
            'saturated identity-to-top chain gives power-of-two size with exponent bounded by orbitals')
    counts['actual_source_invariant_equivalences'] += len(equivalences)


def fibre_and_palette_controls(counts, witnesses):
    for name, n, colour in finite_fibre_models():
        # Freeze the function table before advancing the model generator.
        table = tuple(tuple(colour(x, y) for y in range(n)) for x in range(n))
        col = lambda x, y: table[x][y]
        group = full_automorphisms(n, col)
        require({g[0] for g in group} == set(range(n)), 'positive finite source is actually transitive')
        require(len(group) & (len(group) - 1) == 0, 'actual full finite group order is a power of two')
        palette = sorted({col(x, y) for x, y in combinations(range(n), 2)})
        d = len(palette)
        codes = []
        for atom in palette:
            partition = bipartition(n, ((x, y) for x, y in combinations(range(n), 2) if col(x, y) == atom))
            require(partition is not None, 'every sampled actual diversity atom graph is bipartite')
            codes.append(partition)
            counts['actual_atom_bipartitions'] += 1
        bitcodes = {x: tuple(c[x] for c in codes) for x in range(n)}
        require(len(set(bitcodes.values())) == n and n <= 2 ** d,
                'atom bipartitions inject a complete atomic carrier into the d-dimensional binary cube')
        counts['palette_binary_code_pairs'] += n * (n - 1) // 2
        actual_source_hasse_controls(n, group, col, palette, counts)
        for base in subsets(range(n)):
            stabilizer = tuple(g for g in group if all(g[x] == x for x in base))
            remaining = set(range(n)) - set(base)
            types = {}
            for x in remaining:
                types.setdefault(tuple(col(x, a) for a in base), set()).add(x)
            require(len(types) <= d ** len(base) if base else len(types) <= 1,
                    'one-point type is determined by one actual diversity colour per anchor')
            for fibre in types.values():
                x = min(fibre)
                require({g[x] for g in stabilizer} == fibre,
                        'realized quantifier-free fibre is the EXACT actual point-stabilizer orbit')
                size = len(fibre)
                require(size & (size - 1) == 0, 'sample finite real fibre has power-of-two cardinality')
                m = size.bit_length() - 1
                fibre_palette = {col(x, y) for x, y in combinations(fibre, 2)}
                require(m <= len(fibre_palette) <= d, 'fibre exponent is at most its actual diversity palette, hence ambient d')
                counts['actual_real_fibre_orbit_size_checks'] += 1
            # Every orbit in these FINITE models is algebraic.
            if base:
                require(n <= len(base) + d ** len(base) * 2 ** d,
                        'actual finite acl is bounded by n_base plus number of types times maximum fibre size')
                counts['finite_acl_uniform_bound_checks'] += 1
            else:
                require(n & (n - 1) == 0 and n <= 2 ** d,
                        'empty-base finite transitive case obeys the power-of-two palette bound')
                counts['empty_base_finite_source_checks'] += 1
        # For small carriers verify homogeneity by all finite injective
        # partial maps, independently of the qf-type orbit computation.
        if n <= 4:
            for domain in subsets(range(n)):
                for values in permutations(range(n), len(domain)):
                    request = dict(zip(domain, values))
                    if all(col(x, y) == col(request[x], request[y]) for x, y in combinations(domain, 2)):
                        require(any(all(g[x] == y for x, y in request.items()) for g in group),
                                'every actual finite partial isomorphism extends in the small positive model')
                        counts['finite_homogeneity_extension_checks'] += 1
        counts['actual_finite_fibre_models'] += 1
        tick()
    witnesses['palette_bound_has_no_transitivity_requirement'] = {
        'construction': 'one actual bipartition bit per diversity atom',
        'complete_atomic_pairs_force_injectivity': True,
        'bound': '|F| <= 2^d',
        'scope': 'bounded injection checks; an alternate consequence, not a new source export'}
    witnesses['no_imaginary_or_AP_only_inheritance_claim'] = {
        'realized_real_one_point_fibres_only': True,
        'arbitrary_imaginary_CCO_or_AP_only_Hasse_not_certified': True}


def main():
    counts, witnesses = Counter(), {}
    graph_walk_controls(counts, witnesses)
    odd_prime_automorphism_controls(counts)
    cauchy_controls(counts)
    group_correspondence_controls(counts, witnesses)
    fibre_and_palette_controls(counts, witnesses)
    print(json.dumps(dict(status='PASS', seconds=round(time.monotonic() - START, 3),
                         scope='bounded finite atom graphs, group actions, real fibres and palette bounds',
                         counts=dict(sorted(counts.items())), witnesses=witnesses,
                         limits='Finite diagnostics only: no unbounded high-girth/chromatic theorem, general semantic CCO or finite-group theorem, imaginary inheritance, AP-only Hasse theorem or Lean proof is certified.'), sort_keys=True))


if __name__ == '__main__':
    signal.alarm(30)
    main()
