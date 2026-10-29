#!/usr/bin/env python3
"""Independent finite diagnostics for the joint-owner tuple lemma.

The positive symmetric structures name EVERY difference in F2^n.  Linear
kernels, quotient colours, actual automorphisms, and the full tuple sets
are computed, not imported from the owner-action/master control scripts.
The cyclic example names directed Z/4 differences and tests a nonsplit
finite quotient action only; it is not a claimed symmetric CCO source.
Negative examples deliberately remove individual premises.  None of these
finite calculations certifies CCO, an actual exact source, a provider, or
ordinary EPPA beyond the explicitly enumerated finite inputs.
"""
from collections import Counter
from itertools import combinations, permutations, product


def require(condition, message):
    if not condition:
        raise AssertionError(message)


class Coloured:
    """A literal finite binary-coloured structure; permutations use point images."""

    def __init__(self, points, colour):
        self.points = tuple(points)
        self.index = {x: i for i, x in enumerate(self.points)}
        require(len(self.index) == len(self.points), 'distinct carrier points')
        self.colour = colour
        self._automorphisms = None

    def image(self, action, point):
        return action[self.index[point]]

    def preserves(self, mapping):
        return (set(mapping) <= set(self.points)
                and set(mapping.values()) <= set(self.points)
                and len(set(mapping.values())) == len(mapping)
                and all(self.colour(x, y) == self.colour(mapping[x], mapping[y])
                        for x, y in product(mapping, repeat=2)))

    def automorphisms(self):
        """Exhaust all anchor images and all consistent further images.

        All-difference colours force each image after the anchor is chosen.
        The same exhaustive backtracking remains valid for refined colours;
        it never supplies a selected translation subgroup as Aut input.
        """
        if self._automorphisms is None:
            result = []

            def visit(mapping):
                if len(mapping) == len(self.points):
                    result.append(tuple(mapping[x] for x in self.points))
                    return
                x = self.points[len(mapping)]
                for y in self.points:
                    if y not in mapping.values():
                        candidate = dict(mapping)
                        candidate[x] = y
                        if self.preserves(candidate):
                            visit(candidate)

            visit({})
            self._automorphisms = tuple(result)
        return self._automorphisms


def descend(source, target, projection, action):
    require(set(projection) == set(source.points), 'total projection')
    require(set(projection.values()) == set(target.points), 'onto projection')
    mapping = {}
    for x in source.points:
        a, b = projection[x], projection[source.image(action, x)]
        require(a not in mapping or mapping[a] == b, 'action preserves quotient kernel')
        mapping[a] = b
    require(target.preserves(mapping), 'descended action preserves quotient colours')
    return tuple(mapping[x] for x in target.points)


def partials(structure, points):
    for size in range(len(points) + 1):
        for domain in combinations(points, size):
            for image in permutations(points, size):
                mapping = dict(zip(domain, image))
                if structure.preserves(mapping):
                    yield mapping


def extends(structure, action, partial):
    return all(structure.image(action, x) == y for x, y in partial.items())


def compose(structure, a, b):
    """Composition a after b, using the structure's literal carrier order."""
    return tuple(structure.image(a, structure.image(b, x)) for x in structure.points)


def project_partial(target, projection, partial):
    result = {}
    for x, y in partial.items():
        a, b = projection[x], projection[y]
        require(a not in result or result[a] == b, 'partial projection is well defined')
        result[a] = b
    require(target.preserves(result), 'partial projection is an injective partial isomorphism')
    return result


def quotient_colour_check(source, target, projection):
    seen = {}
    for x, y in product(source.points, repeat=2):
        colour = source.colour(x, y)
        data = projection[x] == projection[y], target.colour(projection[x], projection[y])
        require(colour not in seen or seen[colour] == data,
                'named fine colour determines kernel and quotient colour')
        seen[colour] = data


def span(basis):
    values = {0}
    for b in basis:
        values |= {x ^ b for x in tuple(values)}
    return frozenset(values)


def join(a, b):
    return frozenset(x ^ y for x in a for y in b)


def representative(kernel, x):
    return min(x ^ k for k in kernel)


def vector_model(n, coordinate_supports, owner_supports, counts, basis=None, seed=None):
    """Supports describe quotient linear kernels, transported by an optional basis.

    The CRT is checked against the ambient vector space independently of
    the Cartesian tuple enumeration.  A finite seed only selects induced
    quotient/owner sets; it is never used as the proposed CRT answer.
    """
    basis = tuple(1 << i for i in range(n)) if basis is None else tuple(basis)
    ambient = tuple(range(1 << n))
    require(len(span(basis)) == len(ambient), 'basis is invertible')
    require(len(coordinate_supports) == len(owner_supports) >= 1, 'nonempty indexed family')
    kernels = [span(b for i, b in enumerate(basis) if not support >> i & 1)
               for support in coordinate_supports]
    owners = [span(b for i, b in enumerate(basis) if not support >> i & 1)
              for support in owner_supports]
    require(all(c <= h for c, h in zip(kernels, owners)), 'C_i <= H_i')
    require(set.intersection(*(set(c) for c in kernels)) == {0}, 'intersection C_i is identity')
    for i, j in combinations(range(len(kernels)), 2):
        require(join(kernels[i], kernels[j]) == join(owners[i], owners[j]), 'JOG holds literally')
        counts['join_gate_pairs'] += 1
    star = frozenset.intersection(*owners)
    seed = ambient if seed is None else tuple(seed)

    def quotient(kernel):
        return Coloured(sorted({representative(kernel, x) for x in seed}),
                        lambda x, y: representative(kernel, x ^ y))

    ds, bs = [quotient(k) for k in kernels], [quotient(h) for h in owners]
    omega = quotient(star)
    r = len(ds)
    bi = [{b: representative(h, b) for b in omega.points} for h in owners]
    di = [{x: representative(h, x) for x in d.points} for d, h in zip(ds, owners)]

    def compatible(t):
        return all(representative(join(owners[i], owners[j]), t[i])
                   == representative(join(owners[i], owners[j]), t[j])
                   for i, j in combinations(range(r), 2))

    owner_tuples = {tuple(p[b] for p in bi) for b in omega.points}
    require(owner_tuples == {t for t in product(*(b.points for b in bs)) if compatible(t)},
            'owner set is exactly the full compatible owner tuple set')
    tuples = tuple(t for t in product(*(d.points for d in ds)) if compatible(t))
    ambient_crt = {}
    for x in ambient:
        t = tuple(representative(c, x) for c in kernels)
        require(t not in ambient_crt, 'CRT coordinate map is injective on the actual source')
        ambient_crt[t] = x
    require(set(tuples) == {t for t in ambient_crt
                           if all(t[i] in d.index for i, d in enumerate(ds))},
            'full formal tuples equal exactly the actual CRT preimages in the induced coordinates')
    w = Coloured(tuples, lambda x, y: ambient_crt[x] ^ ambient_crt[y])
    wd = [{t: t[i] for t in tuples} for i in range(r)]
    wo = {t: representative(star, ambient_crt[t]) for t in tuples}
    require(set(wo.values()) == set(omega.points), 'W projects exactly onto B_Omega')
    require(all(set(p.values()) == set(d.points) for p, d in zip(wd, ds)),
            'every coordinate projection W -> D_i is onto')
    counts['models'] += 1
    counts['actual_structures'] += 2 * r + 2
    counts['witness_points'] += len(tuples)
    check_groups(w, ds, bs, omega, wd, wo, di, bi, counts)


def check_groups(w, ds, bs, omega, wd, wo, di, bi, counts):
    aw, gamma = w.automorphisms(), omega.automorphisms()
    ads, abs_ = [d.automorphisms() for d in ds], [b.automorphisms() for b in bs]
    for source, target, projection in [(w, omega, wo)] + list(zip([w] * len(ds), ds, wd)):
        quotient_colour_check(source, target, projection)
    colour_meet = {}
    for x, y in product(w.points, repeat=2):
        colours = tuple(d.colour(p[x], p[y]) for d, p in zip(ds, wd))
        fine = w.colour(x, y)
        require(colours not in colour_meet or colour_meet[colours] == fine,
                'the complete coordinate colour tuple reconstructs every original fine colour')
        colour_meet[colours] = fine
        counts['fine_colour_meet_pairs'] += 1
    own = []
    for d, b, p, actions in zip(ds, bs, di, ads):
        quotient_colour_check(d, b, p)
        own.append({a: descend(d, b, p, a) for a in actions})
    rho = [{g: descend(omega, b, p, g) for g in gamma} for b, p in zip(bs, bi)]
    owner_patterns = {}
    for g in gamma:
        pattern = tuple(p[g] for p in rho)
        require(pattern not in owner_patterns, 'common owner action is unique')
        owner_patterns[pattern] = g
    compatible = {}
    for alpha in product(*ads):
        pattern = tuple(p[a] for p, a in zip(own, alpha))
        if pattern in owner_patterns:
            compatible[alpha] = owner_patterns[pattern]
    actual = {}
    w_owner = {}
    for a in aw:
        components = tuple(descend(w, d, p, a) for d, p in zip(ds, wd))
        require(components not in actual, 'coordinate actions determine actual W action')
        actual[components] = a
        w_owner[a] = descend(w, omega, wo, a)
    require(set(actual) == set(compatible), 'ENTIRE actual Aut(W) equals the finite group pullback')
    for components, g in compatible.items():
        mapping = {x: tuple(d.image(a, x[i]) for i, (d, a) in enumerate(zip(ds, components)))
                   for x in w.points}
        require(w.preserves(mapping), 'compatible tuple preserves every original fine colour')
        require(tuple(mapping[x] for x in w.points) == actual[components], 'literal tuple lift is actual')
        require(w_owner[actual[components]] == g, 'lift has the unique exact global owner action')
    for components, a in actual.items():
        for components_b, b in actual.items():
            composed = tuple(compose(d, ai, bi_) for d, ai, bi_ in zip(ds, components, components_b))
            ab = compose(w, a, b)
            require(composed in actual and actual[composed] == ab,
                    'pullback identity respects actual group multiplication')
            require(w_owner[ab] == compose(omega, w_owner[a], w_owner[b]),
                    'global owner component is an actual group homomorphism')
            counts['group_compositions'] += 1
    for d, b, p, actions, owner in zip(ds, bs, di, ads, own):
        for x, y, delta in product(d.points, d.points, b.automorphisms()):
            if b.image(delta, p[x]) == p[y]:
                require(any(owner[a] == delta and d.image(a, x) == y for a in actions),
                        'coordinate prescribed-owner point homogeneity premise')
                counts['coordinate_point_requests'] += 1
    require(set(w_owner.values()) == set(gamma), 'actual W -> Gamma map is onto, also when empty')
    kernel = [a for a in aw if w_owner[a] == omega.points]
    for x, y in product(w.points, repeat=2):
        if wo[x] == wo[y]:
            require(any(w.image(a, x) == y for a in kernel), 'kernel transitive on each full owner fibre')
            counts['kernel_pairs'] += 1
        for g in gamma:
            if omega.image(g, wo[x]) == wo[y]:
                require(any(w_owner[a] == g and w.image(a, x) == y for a in aw),
                        'every prescribed global owner action and point image lifts')
                counts['joint_point_requests'] += 1
    counts['actual_automorphisms'] += len(aw) + len(gamma) + sum(map(len, ads)) + sum(map(len, abs_))
    counts['pullback_elements'] += len(compatible)
    check_eppa(w, ds, bs, omega, wd, wo, di, aw, ads, gamma, own, rho, actual, counts)
    check_rooted_transport(w, ds, bs, omega, wd, wo, bi, ads, gamma, own, rho, actual, counts)


def check_eppa(w, ds, bs, omega, wd, wo, di, aw, ads, gamma, own, rho, lifts, counts):
    # Inputs are induced sparse subsets of W, never substituted for the full witness.
    sizes = sorted({0, min(1, len(w.points)), min(3, len(w.points)), min(4, len(w.points))})
    for size in sizes:
        source = w.points[:size]
        projected = [tuple(dict.fromkeys(p[x] for x in source)) for p in wd]
        for d, b, points, p, actions, owner in zip(ds, bs, projected, di, ads, own):
            for partial in partials(d, points):
                for delta in b.automorphisms():
                    if all(b.image(delta, p[x]) == p[y] for x, y in partial.items()):
                        require(any(owner[a] == delta and extends(d, a, partial) for a in actions),
                                'each finite coordinate provider supplies every exact-owner request')
                        counts['relative_partial_requests'] += 1
        owner_input = tuple(dict.fromkeys(wo[x] for x in source))
        for partial in partials(omega, owner_input):
            require(any(extends(omega, g, partial) for g in gamma), 'finite owner input has extensions')
        for partial in partials(w, source):
            po = project_partial(omega, wo, partial)
            pcs = [project_partial(d, p, partial) for d, p in zip(ds, wd)]
            owners = [g for g in gamma if extends(omega, g, po)]
            require(owners, 'projected sparse input owner partial map extends')
            for g in owners:
                choices = [[a for a in actions if owner[a] == rr[g] and extends(d, a, pc)]
                           for d, actions, owner, rr, pc in zip(ds, ads, own, rho, pcs)]
                require(all(choices), 'all requested coordinate extensions actually exist')
                for components in product(*choices):
                    require(extends(w, lifts[components], partial), 'assembled tuple extends original sparse partial map')
                    counts['assembled_extensions'] += 1
            counts['sparse_partial_maps'] += 1
        counts['finite_inputs'] += 1


def check_rooted_transport(w, ds, bs, omega, wd, wo, bi, ads, gamma, own, rho, lifts, counts):
    """Bounded conditional transport, retaining a GIVEN exceptional map.

    The targets below are literal compatible coordinate targets T.  These
    finite packet calculations do not identify T with any actual closure,
    nor supply an unsafe-clique theorem or a rooted source provider.
    """
    if len(ds) < 2 or len(w.points) < 2:
        return
    z, other = w.points[0], w.points[-1]
    complex_ = (z, other)
    for exceptional, (d, actions) in enumerate(zip(ds, ads)):
        supplied = next((a for a in actions if a != d.points), None)
        if supplied is None:
            continue
        # Check the extra M3 owner premise on the actual owner action.  It
        # is a quotient point-lifting property, not a choice of section.
        components = rho[exceptional]
        b_e, projection = bs[exceptional], bi[exceptional]
        require(set(components.values()) == set(b_e.automorphisms()), 'exceptional owner action is onto')
        owner_kernel = [g for g in gamma if components[g] == b_e.points]
        for b, c in product(omega.points, repeat=2):
            if projection[b] == projection[c]:
                require(any(omega.image(g, b) == c for g in owner_kernel),
                        'exceptional owner-action kernel is transitive on each fibre')
                counts['rooted_owner_kernel_pairs'] += 1

        # A0 is a sparse original input, with ONE selected a having the
        # required exceptional root coordinate.  The supplied alpha_e is
        # fixed before choosing a or the common owner action.
        exceptional_root = d.image(supplied, z[exceptional])
        candidates = [a for a in w.points if a[exceptional] == exceptional_root]
        require(candidates, 'given exceptional root image occurs in an original point')
        selected = candidates[-1]
        a0 = (selected,)
        exceptional_target = {d.image(supplied, x[exceptional]) for x in complex_}
        require(exceptional_root in {a[exceptional] for a in a0},
                'given exceptional map already sends root into projection_e(A0)')
        delta = own[exceptional][supplied]
        refinements = [g for g in gamma if components[g] == delta
                       and omega.image(g, wo[z]) == wo[selected]]
        require(refinements, 'M3 refines the ENTIRE exceptional owner component and joint root image')
        common = refinements[0]
        chosen = [None] * len(ds)
        chosen[exceptional] = supplied
        targets = [None] * len(ds)
        targets[exceptional] = exceptional_target
        for j, coordinate in enumerate(ds):
            if j == exceptional:
                continue
            # Invariant packets are computed from a linear span of the
            # projected differences.  Their invariance is then verified
            # against EVERY actual coordinate automorphism.
            packet_kernel = span(x[j] ^ z[j] for x in complex_)

            def packet(point):
                return {x for x in coordinate.points if x ^ point in packet_kernel}

            require(all(x[j] in packet(z[j]) for x in complex_), 'nonexceptional projection is in one packet')
            for action in ads[j]:
                for x, y in product(coordinate.points, repeat=2):
                    require(((x ^ y) in packet_kernel)
                            == ((coordinate.image(action, x) ^ coordinate.image(action, y)) in packet_kernel),
                            'F_j is an invariant equivalence for every actual coordinate automorphism')
            matches = [a for a in ads[j] if own[j][a] == rho[j][common]
                       and coordinate.image(a, z[j]) == selected[j]]
            require(matches, 'nonexceptional root lift has the exact common owner action')
            chosen[j] = matches[0]
            targets[j] = set().union(*(packet(a[j]) for a in a0))
            require({coordinate.image(chosen[j], x) for x in packet(z[j])} == packet(selected[j]),
                    'chosen coordinate map transports the complete invariant root packet')
            require(packet(selected[j]) <= targets[j], 'A_j contains F_j[projection_j(A0)]')
            if 1 < len(packet(z[j])) < len(coordinate.points):
                counts['rooted_proper_nontrivial_packets'] += 1

        require(tuple(chosen) in lifts, 'given exceptional map and chosen other maps assemble')
        assembled = lifts[tuple(chosen)]
        require(descend(w, d, wd[exceptional], assembled) == supplied,
                'assembly retains the EXACT given exceptional automorphism on its entire carrier')
        require(descend(w, omega, wo, assembled) == common,
                'assembled map has the exact common global owner action')
        require(w.image(assembled, z) == selected and selected in a0,
                'assembled original root maps to the ONE selected original A0 point')
        target = {x for x in w.points if all(x[j] in targets[j] for j in range(len(ds)))}
        require({w.image(assembled, x) for x in complex_} <= target,
                'entire multipoint complex maps into the compatible coordinate target T')
        counts['rooted_transport_cases'] += 1
        counts['rooted_retained_exceptional_entries'] += len(supplied)
        counts['rooted_complex_points'] += len(complex_)
        counts['rooted_owner_refinements'] += len(refinements)
        if len(target) < len(w.points):
            counts['rooted_proper_targets'] += 1


def nonsplit(counts):
    source = Coloured(range(4), lambda x, y: (y - x) % 4)
    owner = Coloured(range(2), lambda x, y: (y - x) % 2)
    projection = {x: x % 2 for x in source.points}
    actions, gamma = source.automorphisms(), owner.automorphisms()
    require(len(actions) == 4 and len(gamma) == 2, 'actual all-difference cyclic groups are C4 and C2')
    components = {a: descend(source, owner, projection, a) for a in actions}
    require(set(components.values()) == set(gamma), 'nonsplit map is onto')
    identity, flip = owner.points, (1, 0)
    candidates = [a for a in actions if components[a] == flip]
    require(len(candidates) == 2, 'both possible lifts of the owner involution enumerated')
    require(all(tuple(source.image(a, source.image(a, x)) for x in source.points) != source.points
                for a in candidates), 'no lift has order two: no group section exists')
    for x, y, g in product(source.points, source.points, gamma):
        if owner.image(g, projection[x]) == projection[y]:
            require(any(components[a] == g and source.image(a, x) == y for a in actions),
                    'nonsplit action still has every prescribed point lift')
            counts['nonsplit_point_requests'] += 1
    require(any(components[a] == identity and source.image(a, 0) == 2 for a in actions),
            'nonsplit kernel is transitive in the even fibre')
    counts['rejected_sections'] += len(candidates)


def negatives(counts):
    # C1=C2=Id, H1=H2=Top: coarse compatibility admits four pairs;
    # actual repeated-coordinate CRT has only the two diagonal pairs.
    formal = set(product(range(2), repeat=2))
    actual = {(x, x) for x in range(2)}
    require(actual < formal and (0, 1) not in actual, 'dropping JOG creates false CRT points')
    counts['negative_missing_join_gate_tuples'] = len(formal - actual)

    # Independent coordinate owners, sparse B_Omega with both projections full.
    sparse_owner = {(0, 0), (0, 1), (1, 0)}
    require(all({b[i] for b in sparse_owner} == {0, 1} for i in range(2)), 'sparse owner projections onto')
    require(sparse_owner < formal, 'without owner fullness W has an owner outside B_Omega')
    sparse_coloured = Coloured(sorted(sparse_owner), lambda x, y: tuple(a ^ b for a, b in zip(x, y)))
    require(len(sparse_coloured.automorphisms()) == 1, 'actual sparse owner group is trivial')
    require({(x ^ 1, y) for x, y in sparse_owner} != sparse_owner,
            'a full owner tuple translation does not restrict to sparse B_Omega')
    counts['negative_extra_owner_tuples'] = len(formal - sparse_owner)
    # Fullness alone cannot compensate for a coordinate not onto its owner.
    d1, d2 = (0,), (0, 1)
    incomplete = {(x, y) for x, y in product(d1, d2) if x == y}
    require({y for _, y in incomplete} < set(d2), 'missing coordinate provider prevents coordinate completion')
    counts['negative_uncompleted_coordinates'] = 1

    # Two coordinates share an owner; genuine coordinate automorphisms need
    # one common Gamma action, not unrelated choices of owner action.
    d = Coloured(range(4), lambda x, y: x ^ y)
    flip_owner = tuple(x ^ 1 for x in d.points)
    require(flip_owner in d.automorphisms() and d.points in d.automorphisms(), 'both coordinate maps are actual')
    compatible = {(x, y) for x, y in product(d.points, repeat=2) if x % 2 == y % 2}
    image = {(d.image(flip_owner, x), y) for x, y in compatible}
    require(image.isdisjoint(compatible), 'unmatched owner actions do not preserve full compatible tuple set')
    counts['negative_unmatched_owner_actions'] = 1

    fine = Coloured(range(8), lambda x, y: (x ^ y, (x & 2) == (y & 4) // 2))
    change = {x: x ^ 2 for x in fine.points}
    require(all(((x ^ y) & 3, (x ^ y) & 5)
                == (((change[x] ^ change[y]) & 3), ((change[x] ^ change[y]) & 5))
                for x, y in product(fine.points, repeat=2)), 'coordinate fine colours preserved by candidate')
    require(not fine.preserves(change), 'extra fine colour prevents reconstruction from coordinate colours')
    require(tuple(change[x] for x in fine.points) not in fine.automorphisms(), 'rejected lift absent from ENTIRE actual group')
    counts['negative_extra_colour_automorphisms'] = len(fine.automorphisms())

    parity = {t for t in product(range(2), repeat=3) if sum(t) % 2 == 0}
    require(all({(t[i], t[j]) for t in parity} == formal for i, j in combinations(range(3), 2)),
            'all sparse shadow pair marginals really are full')
    require(len(set(product(range(2), repeat=3)) - parity) == 4,
            'all pair marginals still miss four globally compatible tuples')
    require({(a ^ 1, b, c) for a, b, c in parity} != parity,
            'a genuine coordinate colour automorphism need not preserve sparse shadows')
    counts['negative_missing_global_tuples'] = 4

    bad = Coloured((0, 1, 2), lambda x, y: x ^ y)
    trivial_owner = Coloured((0,), lambda x, y: 0)
    require(trivial_owner.automorphisms() == ((0,),), 'owner has its unique exact action available')
    partial = {0: 1}
    require(bad.preserves(partial), 'missing-provider request is a genuine partial automorphism')
    require(not any(extends(bad, a, partial) for a in bad.automorphisms()),
            'a finite induced coordinate without its provider cannot certify EPPA assembly')
    counts['negative_unprovided_partial_requests'] = 1


def main():
    counts = Counter()
    # Supports are quotient coordinates; kernels are their complementary
    # linear spans, not assumed formal equivalence names.
    examples = [
        (1, (1,), (0,)),
        (3, (7,), (1,)),
        (3, (3, 5), (1, 1)),
        (3, (3, 5), (3, 1)),
        (3, (1, 2, 4), (0, 0, 0)),
        (3, (1, 2, 4), (1, 2, 4)),
        (3, (3, 5, 3), (3, 1, 3)),
        (3, (1, 2, 4, 1), (1, 0, 4, 1)),
    ]
    for n, ds, os in examples:
        vector_model(n, ds, os, counts)
    # A noncoordinate linear basis prevents reliance on literal bit masks.
    vector_model(3, (3, 5, 3), (3, 1, 3), counts, basis=(1, 3, 7))
    # Proper finite induced witness with one fixed owner and nontrivial fibres.
    vector_model(3, (3, 5), (1, 1), counts, seed=(1, 3, 5, 7))
    for ds, os in [((7,), (0,)), ((1, 2, 4), (0, 0, 0))]:
        vector_model(3, ds, os, counts, seed=())
    nonsplit(counts)
    negatives(counts)
    require(counts['rooted_transport_cases'] > 0 and counts['rooted_proper_nontrivial_packets'] > 0,
            'conditional rooted controls exercise nontrivial supplied maps and proper multipoint packets')
    print('Joint-owner finite controls passed (stdlib; carriers <=8; r=1..4; repeated kernels; empty witnesses).')
    for key, value in sorted(counts.items()):
        print(f'  {key}: {value}')
    print('Full actual colour automorphism pullbacks and point lifts; sparse-input finite assembly; '
          'conditional retained-exceptional-map transport into coordinate targets only. '
          'No CCO, actual-exact-source, provider, or unrestricted ordinary-EPPA certification.')


if __name__ == '__main__':
    main()
