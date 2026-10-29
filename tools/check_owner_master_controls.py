#!/usr/bin/env python3
"""Exhaustive small finite controls for the upset-indexed master construction.

All labelled posets on <=4 points, all larger-first addition orders, and
all DISTINCT upset families are tested.  Families are joined independently
of the proposed union space: their pair-compatible tuples are encoded by
their merged coordinate assignment, with an explicit inverse.  Memoization
reuses identical relational joins and induction reconstruction maps, never
a proposed union-space answer as the result of a relational join.

The full model is X_U=F2^U with every difference a named binary colour.
The second set/projection model has successor-dependent one/two-point
fibres, built recursively as FULL fibre products over complete owner images.
It is deliberately not claimed to have the automorphism/EPPA premises.
Only the full difference model supplies the actual-group M3 controls.
Neither model certifies CCO, arbitrary EPPA, finite-packet closure, a source
provider, or the unrestricted owner-master theorem.
"""
from collections import Counter
from itertools import combinations, permutations, product


def require(value, message):
    if not value:
        raise AssertionError(message)


def bits(mask):
    while mask:
        bit = mask & -mask
        yield bit
        mask ^= bit


def assignments(mask):
    """All F2 assignments, encoded in the ambient labelled coordinates."""
    result = [0]
    for bit in bits(mask):
        result += [x | bit for x in result]
    return tuple(sorted(result))


def labelled_posets(n):
    pairs = tuple(combinations(range(n), 2))
    for choices in product(range(3), repeat=len(pairs)):
        above = [0] * n
        for (p, q), choice in zip(pairs, choices):
            if choice == 1:
                above[p] |= 1 << q
            elif choice == 2:
                above[q] |= 1 << p
        if all(not (above[q] & ~above[p])
               for p in range(n) for q in range(n) if above[p] >> q & 1):
            yield tuple(above)


def upsets(above, within):
    return tuple(u for u in range(within + 1) if not u & ~within
                 and all(not (above[p] & ~u) for p in range(len(above)) if u >> p & 1))


def addition_orders(above):
    for order in permutations(range(len(above))):
        seen = 0
        for p in order:
            if above[p] & ~seen:
                break
            seen |= 1 << p
        else:
            yield order


def local_fibres(owner_space, pbit, owner, contextual):
    """Every owner survives; the permitted p-values may depend on its value."""
    return tuple(sorted(x | value for x in owner_space
                        for value in (0, pbit)
                        if not (contextual and owner and value and x.bit_count() % 2)))


def construct(above, order, contextual, counts):
    spaces = {0: (0,)}
    stage = 0
    for p in order:
        bit, owner = 1 << p, above[p]
        require(not owner & ~stage, 'successors are already present')
        local = local_fibres(spaces[owner], bit, owner, contextual)
        require({x & owner for x in local} == set(spaces[owner]),
                'the local owner image is complete')
        if contextual and owner:
            fibre_sizes = {sum(x & owner == b for x in local) for b in spaces[owner]}
            require(fibre_sizes == {1, 2}, 'context-dependent fibres really vary with the owner')
            counts['context_dependent_steps'] += 1
        old_spaces = dict(spaces)
        for v in upsets(above, stage | bit):
            if not v & bit:
                continue
            old = v ^ bit
            pairs = [(b, x) for b in old_spaces[old] for x in local
                     if b & owner == x & owner]
            joined = tuple(sorted(b | x for b, x in pairs))
            require(len(set(joined)) == len(pairs), 'full-product coordinate map is injective')
            require({b for b, _ in pairs} == set(old_spaces[old])
                    and {x for _, x in pairs} == set(local), 'both product maps are onto')
            spaces[v] = joined
            counts['constructed_products'] += 1
            counts['constructed_points'] += len(joined)
        stage |= bit
        require(all(spaces[v] == points for v, points in old_spaces.items()),
                'every previously prepared space is unchanged')
        counts['stages'] += 1
    return spaces


def check_projections(above, spaces, contextual, counts):
    """Check all canonical maps, their composites, and all binary CRT squares."""
    us = tuple(spaces)
    for u in us:
        require(all(x & u == x for x in spaces[u]), 'points have exactly their available coordinates')
        for v in us:
            if v & ~u:
                continue
            require({x & v for x in spaces[u]} == set(spaces[v]), 'canonical projection is onto')
            counts['projections'] += 1
            for w in us:
                if not w & ~v:
                    require(all((x & v) & w == x & w for x in spaces[u]),
                            'all canonical projection triangles commute')
                    counts['triangles'] += 1
    for u, v in product(us, repeat=2):
        overlap, union = u & v, u | v
        compatible = {(a, b) for a in spaces[u] for b in spaces[v]
                      if a & overlap == b & overlap}
        image = {(x & u, x & v) for x in spaces[union]}
        require(image == compatible and len(image) == len(spaces[union]),
                'binary product has every compatible pair exactly once and no extras')
        counts['binary_squares'] += 1
        counts['binary_tuples'] += len(compatible)
    # This reference is a direct restriction of the ambient F2 assignment
    # set, not the recursive construction used above.
    for u, points in spaces.items():
        direct = tuple(x for x in assignments(u)
                       if all(not (x >> p & 1 and above[p]
                                   and (x & above[p]).bit_count() % 2)
                              for p in range(len(above)) if u >> p & 1))
        if contextual:
            require(points == direct, 'recursive context fibres equal direct local constraints')
        else:
            require(points == assignments(u), 'full model is the literal F2 coordinate space')


def check_families(above, spaces, counts):
    # Larger supports first makes independent relational joins inexpensive.
    us = tuple(sorted(spaces, key=lambda u: (-u.bit_count(), u)))
    size = 1 << len(us)
    covers, relations = [0] * size, [None] * size
    relations[0] = (0,)
    join_cache, reconstruction_cache = {}, set()

    def join(covered, old_relation, v):
        counts['join_requests'] += 1
        key = covered, old_relation, v
        if key not in join_cache:
            overlap = covered & v
            pairs = [(a, b) for a in old_relation for b in spaces[v]
                     if a & overlap == b & overlap]
            merged = tuple(sorted(a | b for a, b in pairs))
            # The merged assignment encodes a tuple bijectively.  Its
            # restrictions recover both operands; no proposed union-space
            # answer is consulted to generate or deduplicate these tuples.
            require(len(set(merged)) == len(pairs), 'independent tuple encoding is injective')
            require(all(((a | b) & covered, (a | b) & v) == (a, b) for a, b in pairs),
                    'merged assignment recovers both compatible coordinates')
            join_cache[key] = merged
            counts['independent_join_pairs'] += len(old_relation) * len(spaces[v])
            counts['independent_joins'] += 1
        return join_cache[key]

    # These incidence checks depend only on the family supports, not its
    # points.  Check them once for every possible p and pair of members.
    last_steps = {}
    for union in us:
        last_steps[union] = tuple(p for p in range(len(above)) if union >> p & 1
                                 and not any(above[q] >> p & 1
                                             for q in range(len(above)) if union >> q & 1))
        for p in last_steps[union]:
            principal = above[p] | (1 << p)
            containing = tuple(v for v in us if not v & ~union and v >> p & 1)
            require(all(not principal & ~v for v in containing),
                    'every p-containing upset contains its whole principal upset')
            require(all(not principal & ~(v & w) for v, w in product(containing, repeat=2)),
                    'every p-containing intersection retains the entire D_p coordinate')
            counts['induction_support_pairs'] += len(containing) ** 2

    require(spaces[0] == (0,), 'empty family is the singleton empty-coordinate quotient')
    counts['families'] += 1
    counts['compatible_tuples'] += 1
    for family in range(1, size):
        index = family.bit_length() - 1
        previous = family ^ (1 << index)
        v, covered = us[index], covers[previous]
        relation = join(covered, relations[previous], v)
        union = covered | v
        covers[family], relations[family] = union, relation
        require(relation == spaces[union],
                'independently enumerated pair-compatible family tuples equal the union image')
        counts['families'] += 1
        counts['compatible_tuples'] += len(relation)
        # Repeat one actual member, with an independently computed join.
        # Self-intersection compatibility forces the repeated point equal.
        require(join(union, relation, v) == relation,
                'repeating a family member adds no tuples and loses none')
        counts['repeated_families'] += 1
        # A merged assignment is a lossless encoding of the whole supplied
        # tuple.  Hence its old-coordinate/common-D_p reconstruction depends
        # only on (union,p,relation), not on the presentation of this family.
        # Test each such map exhaustively and reuse it for every family.
        for p in last_steps[union]:
            key = union, p, relation
            if key not in reconstruction_cache:
                bit, owner = 1 << p, above[p]
                principal, old_union = owner | bit, union ^ bit
                for x in relation:
                    old_point, local_point = x & old_union, x & principal
                    require(old_point in spaces[old_union] and local_point in spaces[principal]
                            and old_point & owner == local_point & owner,
                            'old glued point and common new point have matching prepared owners')
                    require(old_point | local_point == x,
                            'old/common-local reconstruction recovers the supplied tuple encoding')
                    # This tests the unique inverse of the actual full
                    # fibre-product coordinate map, not just membership.
                    candidates = [(b, d) for b in spaces[old_union] for d in spaces[principal]
                                  if b & owner == d & owner and b | d == x]
                    require(candidates == [(old_point, local_point)],
                            'the induction lift is unique and has no extra representations')
                    counts['induction_tuple_checks'] += 1
                reconstruction_cache.add(key)
                counts['induction_reconstruction_maps'] += 1
            counts['induction_tuple_instances'] += len(relation)
            counts['induction_family_steps'] += 1


def actual_difference_actions(mask):
    """Enumerate actual colour automorphisms by all possible anchor images.

    All-difference colours determine each other image from an anchor, but
    we search its possible images and check every ordered-pair colour.
    Thus we do not supply an abstract translation group as input.
    """
    points = assignments(mask)
    actions = []
    for anchor in points:
        mapping = {}
        for x in points:
            candidates = [y for y in points if x ^ points[0] == y ^ anchor]
            require(len(candidates) == 1, 'anchor colour forces exactly one image')
            mapping[x] = candidates[0]
        if len(set(mapping.values())) == len(points) and all(
                x ^ y == mapping[x] ^ mapping[y] for x in points for y in points):
            actions.append(tuple(mapping[x] for x in points))
    require(len(actions) == len(points), 'actual all-difference group has the expected order')
    return points, tuple(actions)


def check_m3(counts):
    models = {mask: actual_difference_actions(mask) for mask in range(16)}
    counts['actual_coloured_sets'] = len(models)
    counts['actual_automorphisms'] = sum(len(actions) for _, actions in models.values())
    for source in range(16):
        points, actions = models[source]
        for target in range(16):
            if target & ~source:
                continue
            owners, owner_actions = models[target]
            index, oindex = {x: i for i, x in enumerate(points)}, {x: i for i, x in enumerate(owners)}
            components = {}
            for action in actions:
                descended = {}
                for x, y in zip(points, action):
                    a, b = x & target, y & target
                    require(a not in descended or descended[a] == b, 'actual action descends consistently')
                    descended[a] = b
                components[action] = tuple(descended[a] for a in owners)
            require(set(components.values()) == set(owner_actions), 'actual quotient action is onto')
            for g, h in product(actions, repeat=2):
                gh = tuple(g[index[hx]] for hx in h)
                og, oh = components[g], components[h]
                require(gh in components and components[gh] == tuple(og[oindex[hx]] for hx in oh),
                        'actual quotient component is a group homomorphism')
                counts['group_compositions'] += 1
            kernel = tuple(g for g in actions if components[g] == owners)
            for x, y in product(points, repeat=2):
                if x & target == y & target:
                    require(any(g[index[x]] == y for g in kernel), 'kernel is transitive on every fibre')
                    counts['kernel_point_pairs'] += 1
                for eta in owner_actions:
                    if eta[oindex[x & target]] == y & target:
                        require(any(components[g] == eta and g[index[x]] == y for g in actions),
                                'every prescribed actual quotient action and point image lifts')
                        counts['prescribed_point_requests'] += 1
            counts['actual_group_maps'] += 1
    # At the step p=2<0, with 1 incomparable, O={0}, old U={0,1}, T={1} is
    # an old target with no factorization T->O.  All maps just checked are
    # actual colour maps, including W={0,1,2}->T and D={0,1}->T.
    d, owner, target, whole = 0b011, 0b001, 0b010, 0b111
    require(any(x & target == y & target and x & owner != y & owner
                for x, y in product(assignments(d), repeat=2)),
            'nonnested old target cannot project to the owner')
    require(not target & ~whole, 'the nonnested target is nevertheless a quotient of the full product')
    counts['nonnested_examples'] += 1


def negative_controls(counts):
    empty_tuple = ()
    bad_empty_object = (0, 1)
    require(len({empty_tuple for _ in bad_empty_object}) == 1
            and len(bad_empty_object) == 2,
            'a nonsingleton empty object fails empty-family CRT injectivity')
    counts['negative_empty_base_excess_points'] += 1
    full = assignments(0b111)
    parity = tuple(x for x in full if x.bit_count() % 2 == 0)
    require(all({x & mask for x in parity} == set(assignments(mask)) for mask in range(7)),
            'parity subset projects onto every proper coordinate set')
    require(all({(x & a, x & b) for x in parity}
                == set(product(assignments(a), assignments(b)))
                for a, b in combinations((1, 2, 4), 2)),
            'all pair projections of three singleton factors are full')
    compatible = set(product((0, 1), (0, 2), (0, 4)))
    image = {(x & 1, x & 2, x & 4) for x in parity}
    require(len(compatible - image) == 4, 'pairwise onto alone misses four global tuples')
    for sparse in (parity, full[:-1]):
        d, c, owner = 0b011, 0b101, 0b001
        ds, cs = {x & d for x in sparse}, {x & c for x in sparse}
        require(ds == set(assignments(d)) and cs == set(assignments(c)),
                'sparse product still projects onto both complete factors')
        pairs = {(a, b) for a in ds for b in cs if a & owner == b & owner}
        actual = {(x & d, x & c) for x in sparse}
        require(actual < pairs, 'removing full-product points breaks binary M4 despite both surjections')
        counts['negative_missing_binary_tuples'] += len(pairs - actual)
    counts['negative_missing_global_tuples'] += len(compatible - image)


def main():
    counts = Counter()
    poset_counts = []
    for n in range(5):
        total = 0
        for above in labelled_posets(n):
            total += 1
            orders = tuple(addition_orders(above))
            require(orders, 'every finite poset has a larger-first order')
            counts['addition_orders'] += len(orders)
            for contextual in (False, True):
                reference = None
                for order in orders:
                    spaces = construct(above, order, contextual, counts)
                    if reference is None:
                        reference = spaces
                    else:
                        require(spaces == reference, 'all addition orders give the same coherent diagram')
                    counts['constructed_diagrams'] += 1
                check_projections(above, reference, contextual, counts)
                check_families(above, reference, counts)
                counts['checked_diagrams'] += 1
        poset_counts.append(total)
    require(poset_counts == [1, 1, 3, 19, 219], 'all labelled posets through four points are covered')
    require(counts['addition_orders'] == 1008, 'all labelled larger-first addition orders are covered')
    check_m3(counts)
    negative_controls(counts)
    print('Owner-master finite controls passed; labelled posets n=0..4: '
          + '/'.join(map(str, poset_counts)) + '. Full F2 and context-dependent fibre diagrams:')
    for name, value in sorted(counts.items()):
        print(f'  {name}: {value}')
    print('All distinct upset families (including empty) and one repeat of every nonempty family; '
          'all addition orders; actual M3 only for the all-difference F2 model. '
          'No CCO, arbitrary EPPA, finite-packet, provider, or master-theorem certification.')


if __name__ == '__main__':
    main()
