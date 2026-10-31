#!/usr/bin/env python3
"""Independent bounded diagnostics for B064's finite interfaces.

No finite model here is claimed terminal, Ramsey, or an unbounded SAP/CCO
source. Actual finite maps test template, coordinate, ordered-amalgam,
same-host restriction and finite-original-source mechanisms separately.
"""
from itertools import combinations, permutations, product
from math import factorial
import json


def subsets(items):
    items = tuple(items)
    for k in range(len(items) + 1):
        yield from combinations(items, k)


def check_templates():
    tables = endomorphisms = automorphisms = omitted_singletons = 0
    witness_tests = postcompositions = core_retractions = 0
    for n in range(4):
        points = tuple(range(n))
        pairs = tuple(product(points, repeat=2))
        profiles = [(0,) * n]
        if n > 1:
            profiles.append((0,) * (n - 1) + (1,))
        for original_sorts in profiles:
            functions = [f for f in product(points, repeat=n)
                         if all(original_sorts[f[x]] == original_sorts[x] for x in points)]
            for mask in range(1 << len(pairs)):
                relation = {pair for i, pair in enumerate(pairs) if mask & (1 << i)}
                # The second old colour has an overlapping universal mask.
                allowed = (relation, set(pairs))
                ends = [f for f in functions if all((f[x], f[y]) in relation for x, y in relation)]
                autos = []
                for f in permutations(points):
                    if not all(original_sorts[f[x]] == original_sorts[x] for x in points):
                        continue
                    inverse = tuple(f.index(x) for x in points)
                    if all((f[x], f[y]) in relation and (inverse[x], inverse[y]) in relation
                           for x, y in relation):
                        autos.append(f)
                assert set(autos) == {f for f in ends if len(set(f)) == n}

                # These are a FAMILY of actual distinct-vertex two-point
                # witnesses, not an asserted complete JEP amalgam of them.
                witnesses = [(2 * i, 2 * i + 1, colour, x, y)
                             for i, (colour, x, y) in enumerate(
                                 (c, x, y) for c in range(2) for x, y in allowed[c])]
                for f in functions:
                    legal = all((f[x], f[y]) in allowed[colour]
                                for left, right, colour, x, y in witnesses if left != right)
                    assert legal == (f in ends)
                    witness_tests += 1
                assert all(left != right for left, right, *_ in witnesses)

                for f in ends:
                    missing = set(points) - set(f)
                    if not missing:
                        continue
                    t = min(missing)
                    # Exhaust ALL legal markings of every two-point old
                    # colour in this table; f postcomposition remains legal
                    # and omits the same realized singleton label t.
                    for colour in range(2):
                        for x, y in allowed[colour]:
                            image = (f[x], f[y])
                            assert image in allowed[colour] and t not in image
                            assert original_sorts[image[0]] == original_sorts[x]
                            assert original_sorts[image[1]] == original_sorts[y]
                            postcompositions += 1
                    omitted_singletons += 1

                # A minimum-rank endomorphism has an idempotent power;
                # independently enumerate endomorphisms of its induced image.
                f = min(ends, key=lambda g: (len(set(g)), g))
                retract = points
                for _ in range(factorial(n)):
                    retract = tuple(f[retract[x]] for x in points)
                image = tuple(sorted(set(retract)))
                assert len(image) == len(set(f))
                assert all(retract[retract[x]] == retract[x] for x in points)
                assert all(retract[x] == x for x in image)
                for values in product(image, repeat=len(image)):
                    g = dict(zip(image, values))
                    if any(original_sorts[g[x]] != original_sorts[x] for x in image):
                        continue
                    if all((g[x], g[y]) in relation for x, y in relation if x in g and y in g):
                        assert len(set(g.values())) == len(image)
                tables += 1
                endomorphisms += len(ends)
                automorphisms += len(autos)
                core_retractions += 1

    # Equal LABELS on distinct vertices really need a stored pair witness.
    relation = {(1, 1)}
    constant_zero = (0, 0)
    assert all((constant_zero[x], constant_zero[y]) in relation
               for x, y in relation if x != y)
    assert not all((constant_zero[x], constant_zero[y]) in relation for x, y in relation)
    return dict(template_tables=tables, actual_endomorphisms=endomorphisms,
                actual_automorphisms=automorphisms, pair_witness_tests=witness_tests,
                singleton_omitting_maps=omitted_singletons,
                legal_pair_postcompositions=postcompositions,
                induced_core_retractions=core_retractions, equal_label_distinct_pair_boundary=1)


def check_equivariant_coordinates():
    coordinate_pairs = holonomy_witnesses = quotient_actions = 0
    for kind, n in [('xor', 1), ('xor', 2), ('xor', 4), ('add', 3)]:
        points = tuple(range(n))
        op = (lambda x, y: x ^ y) if kind == 'xor' else (lambda x, y: (x + y) % n)
        # Actual regular G-orbitals; decide the symmetry hypothesis directly.
        orbitals = {frozenset((op(g, x), op(g, y)) for g in points)
                    for x, y in product(points, repeat=2)}
        symmetric = all(orbital == frozenset((y, x) for x, y in orbital) for orbital in orbitals)
        subgroups = [set(h) for h in subsets(points) if 0 in h
                     and all(op(x, y) in h for x, y in product(h, repeat=2))]
        for subgroup in subgroups:
            cosets = sorted({frozenset(op(x, h) for h in subgroup) for x in points}, key=lambda c: min(c))
            which = {x: i for i, coset in enumerate(cosets) for x in coset}
            carrier = tuple(range(len(cosets)))
            action = lambda g, b: which[op(g, min(cosets[b]))]
            maps = [f for f in product(carrier, repeat=n) if set(f) == set(carrier)
                    and all(f[op(g, x)] == action(g, f[x]) for g, x in product(points, repeat=2))]
            for tau, sigma in product(maps, repeat=2):
                if not symmetric:
                    continue
                assert all((tau[x] == tau[y]) == (sigma[x] == sigma[y])
                           for x, y in product(points, repeat=2))
                factor = {}
                for x in points:
                    assert tau[x] not in factor or factor[tau[x]] == sigma[x]
                    factor[tau[x]] = sigma[x]
                assert len(set(factor.values())) == len(carrier)
                assert all(factor[factor[b]] == b for b in carrier)
                coordinate_pairs += 1
            for f in permutations(carrier):
                if not all(f[action(g, b)] == action(g, f[b]) for g in points for b in carrier):
                    continue
                if f == carrier:
                    continue
                cycles = []
                unseen = set(carrier)
                while unseen:
                    b = min(unseen)
                    cycle, x = set(), b
                    while x not in cycle:
                        cycle.add(x)
                        x = f[x]
                    assert x == b
                    unseen -= cycle
                    cycles.append(cycle)
                lengths = {len(cycle) for cycle in cycles}
                assert len(lengths) == 1 and next(iter(lengths)) > 1
                block = {b: i for i, cycle in enumerate(cycles) for b in cycle}
                assert all((block[b] == block[c]) == (block[action(g, b)] == block[action(g, c)])
                           for g in points for b, c in product(carrier, repeat=2))
                # Its finite cycle equivalence pulls back above the quotient
                # kernel with exactly this nontrivial finite relative index.
                for cycle in cycles:
                    pulled_back = {x for x in points if which[x] in cycle}
                    assert len({which[x] for x in pulled_back}) == next(iter(lengths))
                holonomy_witnesses += 1
            quotient_actions += 1
    # Without symmetric invariant relations, a regular C3 translation has
    # order three and is an actual counterexample to the involution claim.
    shift = (1, 2, 0)
    assert any(shift[shift[x]] != x for x in range(3))
    assert all(shift[shift[shift[x]]] == x for x in range(3))
    return dict(actual_quotient_actions=quotient_actions,
                symmetric_equivariant_coordinate_pairs=coordinate_pairs,
                finite_holonomy_index_witnesses=holonomy_witnesses,
                nonsymmetric_coordinate_boundary=1)


def hidden_points(roots):
    return ({('J', *x) for x in roots} | {('T', *x) for x in roots}
            | {('U', x[0]) for x in roots} | {('V', x[1]) for x in roots})


def unary(name, point):
    if name == 'f' and point[0] == 'J':
        return ('T', *point[1:])
    if name == 'g' and point[0] == 'T':
        return ('J', *point[1:])
    if name == 'u' and point[0] in {'J', 'T'}:
        return ('U', point[1])
    if name == 'v' and point[0] in {'J', 'T'}:
        return ('V', point[2])
    return None


def normalized_order(roots, u_order, v_order, fibres):
    ur, vr = ({x: i for i, x in enumerate(order)} for order in (u_order, v_order))
    priority = {'U': 0, 'V': 1, 'J': 2, 'T': 3}
    def key(p):
        if p[0] == 'U':
            return priority[p[0]], ur[p[1]]
        if p[0] == 'V':
            return priority[p[0]], vr[p[1]]
        _, a, b, c = p
        # Deliberately different parent priorities in the transition copy:
        # synchronization concerns fibre tasks, not whole-sort monotonicity.
        parents = (ur[a], vr[b]) if p[0] == 'J' else (vr[b], ur[a])
        return (priority[p[0]], *parents, fibres[a, b].index(c))
    return tuple(sorted(hidden_points(roots), key=key))


def actual_pair_code(order, p, q):
    """Complete tests in this finite named-function/coordinate language."""
    rank = {x: i for i, x in enumerate(order)}
    coordinate_pair = p[0] in {'J', 'T'} and q[0] in {'J', 'T'}
    semantic = (p[1] == q[1], p[2] == q[2], p[1:] == q[1:]) if coordinate_pair else ()
    return (p[0], q[0], p == q, semantic, rank[p] < rank[q],
            tuple((unary(f, p) is not None, unary(f, p) == q) for f in ('f', 'g', 'u', 'v')))


def closure(generators):
    closed = set(generators)
    while True:
        more = {unary(f, p) for p in closed for f in ('f', 'g', 'u', 'v')} - {None}
        if more <= closed:
            return closed
        closed |= more


def check_ordered_amalgams():
    u, v, z, extra = ((0, 0, c) for c in (0, 2, 1, 3))
    left = {u, v, extra, (0, 1, 0), (1, 0, 0)}
    right = {u, v, z, (0, 2, 0), (2, 0, 0)}
    base = hidden_points({u, v})
    assert closure({('J', *u), ('J', *v)}) == base
    assert closure({('J', *u), ('J', *v), ('J', *z)}) - base == {('J', *z), ('T', *z)}
    assert hidden_points(left) & hidden_points(right) == base
    union = left | right
    points = hidden_points(union)
    assert all(unary(f, p) is None or unary(f, p) in points
               for f in ('f', 'g', 'u', 'v') for p in points)
    # Equal ALL parent coordinates, rather than one selected coordinate,
    # determine a merged parent fibre across the strong closed-base span.
    for x in left:
        for y in right:
            if x[:2] == y[:2]:
                assert ('U', x[0]) in base and ('V', x[1]) in base
    assert (0, 1, 0)[0] == (0, 2, 0)[0] and (0, 1, 0)[:2] != (0, 2, 0)[:2]
    span_orders = amalgams = code_checks = pair_codes = 0
    for ua, va, ut, vt in product(permutations((0, 1)), permutations((0, 1)),
                                   permutations((0, 2)), permutations((0, 2))):
        for fibre_left in permutations((0, 2, 3)):
            if fibre_left.index(0) > fibre_left.index(2):
                continue
            af = {(0, 0): fibre_left, (0, 1): (0,), (1, 0): (0,)}
            tf = {(0, 0): (0, 1, 2), (0, 2): (0,), (2, 0): (0,)}
            ao, to = normalized_order(left, ua, va, af), normalized_order(right, ut, vt, tf)
            assert tuple(p for p in ao if p in base) == tuple(p for p in to if p in base)
            found = 0
            u_extensions = [o for o in permutations((0, 1, 2))
                            if tuple(x for x in o if x in ua) == ua and tuple(x for x in o if x in ut) == ut]
            v_extensions = [o for o in permutations((0, 1, 2))
                            if tuple(x for x in o if x in va) == va and tuple(x for x in o if x in vt) == vt]
            f_extensions = [o for o in permutations((0, 1, 2, 3))
                            if tuple(x for x in o if x in fibre_left) == fibre_left
                            and tuple(x for x in o if x in (0, 1, 2)) == (0, 1, 2)]
            for ue, ve, fe in product(u_extensions, v_extensions, f_extensions):
                fibres = {**af, **tf, (0, 0): fe}
                joined = normalized_order(union, ue, ve, fibres)
                assert tuple(p for p in joined if p in set(ao)) == ao
                assert tuple(p for p in joined if p in set(to)) == to
                rank = {p: i for i, p in enumerate(joined)}
                assert rank[('J', *u)] < rank[('J', *z)] < rank[('J', *v)]
                assert ('J', *z) not in hidden_points(left)
                # m is the actual complete within-parent diversity relation
                # here; check the two reset edges and the whole old code.
                assert u[:2] == z[:2] == v[:2] and u != z != v
                for factor_order in (ao, to):
                    factor = set(factor_order)
                    for p, q in product(factor_order, repeat=2):
                        assert actual_pair_code(factor_order, p, q) == actual_pair_code(joined, p, q)
                        pair_codes += 1
                    for p in factor:
                        for f in ('f', 'g', 'u', 'v'):
                            assert unary(f, p) is None or unary(f, p) in factor
                            code_checks += 1
                found += 1
            assert found
            span_orders += 1
            amalgams += found
    return dict(ordered_closed_spans=span_orders, actual_order_shuffles=amalgams,
                preserved_function_domain_values=code_checks,
                preserved_complete_pair_codes=pair_codes, full_parent_key_boundary=1)


def check_fixed_host_and_finite_sources():
    composition_hosts = composition_competitors = 0
    # K0 finite pure sets, K1 linear orders, K2 additionally the definable
    # reverse-order relation. All maps below are actual relation-only maps.
    for size in range(1, 5):
        fixed_host = tuple(range(size + 1))
        for competitor in permutations(fixed_host):
            rank = {x: i for i, x in enumerate(competitor)}
            selected = competitor[:size]
            embedding = dict(enumerate(selected))
            assert all((i < j) == (rank[embedding[i]] < rank[embedding[j]])
                       and (i > j) == (rank[embedding[i]] > rank[embedding[j]])
                       for i, j in product(range(size), repeat=2))
            composition_competitors += 1
        composition_hosts += 1
    # Existential choice of a favorite free-unary expansion is weaker than
    # the required EVERY-competitor quantifier on this exact fixed host.
    fixed = tuple(range(3))
    successes = [marks for marks in product(range(2), repeat=len(fixed)) if set(marks) == {0, 1}]
    assert successes and (0, 0, 0) not in successes

    arrows = reasons = unique_maps = 0
    for n in range(1, 5):
        q = tuple(range(n))
        colour = (lambda x, y: x ^ y) if n == 4 else (lambda x, y: int(x != y))
        def embeddings(source, target):
            for values in permutations(target, len(source)):
                f = dict(zip(source, values))
                if all(colour(x, y) == colour(f[x], f[y]) for x, y in product(source, repeat=2)):
                    yield f
        autos = tuple(embeddings(q, q))
        pieces = tuple(subsets(q))
        labels = {a: tuple(embeddings(a, q)) for a in pieces}
        for a in pieces:
            for source_labels, host_labels in product(labels[a], autos):
                candidates = [f for f in embeddings(a, q)
                              if all(host_labels[f[x]] == source_labels[x] for x in a)]
                assert len(candidates) == 1
                arrows += 1
                unique_maps += len(candidates)
            for b in pieces:
                for f in embeddings(a, b):
                    for prescribed in labels[a]:
                        extensions = [lab for lab in labels[b]
                                      if all(lab[f[x]] == prescribed[x] for x in a)]
                        assert extensions
                        reasons += 1
    return dict(relation_only_fixed_hosts=composition_hosts,
                every_competing_order_checked=composition_competitors,
                favorite_unary_expansion_boundary=1,
                finite_original_EP_arrows=arrows,
                unique_label_preserving_embeddings=unique_maps,
                same_embedding_label_extensions=reasons)


def main():
    result = {}
    for check in (check_templates, check_equivariant_coordinates,
                  check_ordered_amalgams, check_fixed_host_and_finite_sources):
        result.update(check())
    result['status'] = 'PASS_BOUNDED_DIAGNOSTICS_ONLY'
    print(json.dumps(result, sort_keys=True))


if __name__ == '__main__':
    main()
