#!/usr/bin/env python3
"""Finite controls for full fibre products and prescribed-owner actions.

The positive colour model is the regular translation structure on F2^3,
with EVERY vector difference a named binary colour.  Its coordinate
quotients are computed literally, not supplied as abstract automorphism
groups.  These finite checks do not prove CCO, arbitrary EPPA, an infinite
provider, or the owner-master theorem.  The extra-relation negative control
is an arbitrary coloured structure, not a claimed actual exact CCO source.
"""
from itertools import combinations, permutations, product


def require(value, message):
    if not value:
        raise AssertionError(message)


def subsets(values):
    values = tuple(values)
    for size in range(len(values) + 1):
        yield from combinations(values, size)


def difference(x, y):
    return tuple(a ^ b for a, b in zip(x, y))


def compose(a, b):
    """Permutation composition a after b."""
    return tuple(a[b[i]] for i in range(len(a)))


def inverse(action):
    return tuple(action.index(i) for i in range(len(action)))


def equivalence_colour(x, y):
    return 0 if x == y else 1 if x[0] == y[0] else 2


class ColouredSet:
    def __init__(self, points, colour=difference):
        self.points = tuple(points)
        self.index = {x: i for i, x in enumerate(self.points)}
        self.colour = colour

    def preserves(self, mapping):
        return (len(set(mapping.values())) == len(mapping)
                and all(self.colour(x, y) == self.colour(mapping[x], mapping[y])
                        for x, y in product(mapping, repeat=2)))

    def automorphisms(self):
        """Exhaust all permutations by backtracking, testing each anchor image.

        For the difference models the colour from the first point determines
        every other image uniquely.  This prunes the 8! search without
        assuming in advance that an automorphism is a translation.  Empty
        points give the single empty permutation.
        """
        result = []

        def visit(mapping):
            if len(mapping) == len(self.points):
                result.append(tuple(self.index[mapping[x]] for x in self.points))
                return
            x = self.points[len(mapping)]
            for y in self.points:
                if y in mapping.values():
                    continue
                candidate = dict(mapping)
                candidate[x] = y
                if self.preserves(candidate):
                    visit(candidate)

        visit({})
        return tuple(result)

    def image(self, action, x):
        return self.points[action[self.index[x]]]

    def permutation(self, mapping):
        require(set(mapping) == set(self.points), 'permutation has full domain')
        require(set(mapping.values()) == set(self.points), 'permutation is onto')
        return tuple(self.index[mapping[x]] for x in self.points)


def induced(source, target, projection, action):
    require(set(projection) == set(source.points), 'quotient map is total')
    require(set(projection.values()) == set(target.points), 'quotient map is onto')
    mapping = {}
    for x in source.points:
        a, b = projection[x], projection[source.image(action, x)]
        require(a not in mapping or mapping[a] == b, 'action descends to quotient')
        mapping[a] = b
    return target.permutation(mapping)


def extends(structure, action, partial):
    return all(structure.image(action, x) == y for x, y in partial.items())


def partial_isometries(structure, points):
    for domain in subsets(points):
        for image in permutations(points, len(domain)):
            mapping = dict(zip(domain, image))
            if structure.preserves(mapping):
                yield mapping


def descend_partial(source, target, projection, partial):
    result = {}
    for x, y in partial.items():
        a, b = projection[x], projection[y]
        require(a not in result or result[a] == b, 'partial map descends consistently')
        result[a] = b
    require(target.preserves(result), 'descended map is an injective partial isometry')
    return result


def check_colour_quotient(source, target, projection):
    """Kernel and quotient colours really are unions of named fine colours."""
    blocks = {}
    for x, y in product(source.points, repeat=2):
        fine = source.colour(x, y)
        data = (projection[x] == projection[y],
                target.colour(projection[x], projection[y]))
        require(fine not in blocks or blocks[fine] == data,
                'fine colour determines quotient kernel and colour')
        blocks[fine] = data


def check_fibre_product(w, d, c, o, wd, wc, do, co):
    aw, ad, ac, ao = (s.automorphisms() for s in (w, d, c, o))
    coordinates = {(wd[x], wc[x]): x for x in w.points}
    full = {(a, b) for a, b in product(d.points, c.points) if do[a] == co[b]}
    require(set(coordinates) == full and len(coordinates) == len(w.points),
            'literal full fibre product, with injective coordinates')
    for source, target, projection in ((w, d, wd), (w, c, wc),
                                        (d, o, do), (c, o, co)):
        check_colour_quotient(source, target, projection)
    od = {g: induced(d, o, do, g) for g in ad}
    oc = {h: induced(c, o, co, h) for h in ac}
    require(set(od.values()) <= set(ao) and set(oc.values()) <= set(ao),
            'coordinate actions induce actual owner automorphisms')
    compatible = {(g, h) for g, h in product(ad, ac) if od[g] == oc[h]}
    actual = {(induced(w, d, wd, f), induced(w, c, wc, f)) for f in aw}
    require(len(actual) == len(aw) and actual == compatible,
            'actual automorphisms equal the compatible coordinate pairs')
    lifts = {}
    for g, h in compatible:
        mapping = {x: coordinates[d.image(g, wd[x]), c.image(h, wc[x])]
                   for x in w.points}
        require(w.preserves(mapping), 'compatible pair preserves original fine colours')
        lifts[g, h] = w.permutation(mapping)
        require(lifts[g, h] in aw, 'coordinate lift is an enumerated actual automorphism')
    return aw, ad, ac, ao, od, oc, lifts


def check_prescribed_lifting(source, target, projection, actions, target_actions):
    images = {g: induced(source, target, projection, g) for g in actions}
    require(set(images.values()) == set(target_actions), 'quotient action is onto')
    identity = tuple(range(len(target.points)))
    kernel = tuple(g for g in actions if images[g] == identity)
    requests = 0
    for x, y in product(source.points, repeat=2):
        if projection[x] == projection[y]:
            require(any(source.image(g, x) == y for g in kernel),
                    'quotient kernel is transitive on each fibre')
        for eta in target_actions:
            if target.image(eta, projection[x]) == projection[y]:
                require(any(images[g] == eta and source.image(g, x) == y for g in actions),
                        'every prescribed quotient action and point image lifts')
                requests += 1
    return len(kernel), requests


def positive_controls():
    w = ColouredSet(product(range(2), repeat=3))
    d, c = (ColouredSet(product(range(2), repeat=2)) for _ in range(2))
    o, t = (ColouredSet([(0,), (1,)]) for _ in range(2))
    wd = {x: x[:2] for x in w.points}
    wc = {x: (x[0], x[2]) for x in w.points}
    do = {x: x[:1] for x in d.points}
    co = {x: x[:1] for x in c.points}
    aw, ad, ac, ao, od, oc, lifts = check_fibre_product(w, d, c, o, wd, wc, do, co)
    require(tuple(map(len, (aw, ad, ac, ao))) == (8, 4, 4, 2),
            'exhaustive actual group orders are 8,4,4,2')
    for structure, actions in ((w, aw), (d, ad), (c, ac), (o, ao)):
        translations = {tuple(structure.index[difference(x, shift)] for x in structure.points)
                        for shift in structure.points}
        require(set(actions) == translations, 'exhaustively found groups equal translations')
    require(len(aw) * len(ao) == len(ad) * len(ac), 'full action order 8 = 4*4/2')
    dt = {x: x[1:] for x in d.points}
    wt = {x: x[1:2] for x in w.points}
    require(any(dt[x] == dt[y] and do[x] != do[y] for x, y in product(d.points, repeat=2)),
            'nonnested T=d has no map to O making D projections factor')
    at = t.automorphisms()
    check_prescribed_lifting(d, t, dt, ad, at)
    check_prescribed_lifting(c, o, co, ac, ao)
    nonnested = check_prescribed_lifting(w, t, wt, aw, at)
    # Nested T=O gives W_T=O x_O C, canonically the actual four-point C.
    nested_t = o
    nested_wt = ColouredSet((owner, point) for owner, point in product(o.points, c.points)
                           if owner == co[point])
    nt_o = {x: x for x in o.points}
    nwt_t = {x: x[0] for x in nested_wt.points}
    nwt_c = {x: x[1] for x in nested_wt.points}
    # Transport precisely C's quotient colour along the canonical bijection.
    nested_wt.colour = lambda x, y: c.colour(x[1], y[1])
    ndata = check_fibre_product(nested_wt, nested_t, c, o,
                               nwt_t, nwt_c, nt_o, co)
    require(len(ndata[0]) == 4, 'nested W_T is the four-point C with actual group order four')
    check_prescribed_lifting(d, o, do, ad, ao)
    nested_owner = check_prescribed_lifting(w, o, {x: x[:1] for x in w.points}, aw, ao)
    nested = check_prescribed_lifting(w, nested_wt,
                                     {x: (x[:1], wc[x]) for x in w.points}, aw, ndata[0])

    sources = [(), ((0, 0, 0),),
               ((0, 0, 0), (0, 1, 0), (1, 0, 1)),
               ((0, 0, 0), (0, 1, 1), (1, 0, 1), (1, 1, 0)),
               ((0, 0, 0), (0, 0, 1), (0, 1, 0), (1, 0, 0), (1, 1, 1))]
    partial_count = ep_pa_requests = prescribed_c_requests = 0
    for source in sources:
        a_d = tuple(sorted({wd[x] for x in source}))
        a_c = tuple(sorted({wc[x] for x in source}))
        for partial in partial_isometries(d, a_d):
            require(any(extends(d, g, partial) for g in ad), 'D has finite EPPA for A_D')
        for partial in partial_isometries(c, a_c):
            for delta in ao:
                if all(o.image(delta, co[x]) == co[y] for x, y in partial.items()):
                    require(any(oc[h] == delta and extends(c, h, partial) for h in ac),
                            'C extends each compatible partial map with exact owner component')
                    prescribed_c_requests += 1
        for partial in partial_isometries(w, source):
            pd = descend_partial(w, d, wd, partial)
            pc = descend_partial(w, c, wc, partial)
            choices = [g for g in ad if extends(d, g, pd)]
            require(choices, 'descended D partial map extends')
            for g in choices:
                delta = od[g]
                require(all(o.image(delta, co[x]) == co[y] for x, y in pc.items()),
                        'chosen D extension gives compatible exact C owner request')
                matches = [h for h in ac if oc[h] == delta and extends(c, h, pc)]
                require(matches, 'C extension matches EXACT chosen D owner component')
                require(all(extends(w, lifts[g, h], partial) for h in matches),
                        'compatible coordinate extensions extend original partial map')
                ep_pa_requests += 1
            partial_count += 1
    return nonnested, nested_owner, nested, len(sources), partial_count, ep_pa_requests, prescribed_c_requests


def empty_controls():
    empty = ColouredSet(())
    data = check_fibre_product(empty, empty, empty, empty, {}, {}, {}, {})
    require(all(actions == ((),) for actions in data[:4]), 'all empty automorphism groups are trivial')
    require(data[-1] == {((), ()): ()}, 'unique compatible empty pair has unique empty lift')
    require(check_prescribed_lifting(empty, empty, {}, ((),), ((),)) == (1, 0),
            'empty quotient action is onto with trivial kernel and no point requests')
    partials = tuple(partial_isometries(empty, ()))
    require(partials == ({},), 'empty source has exactly its empty partial isometry')
    require(descend_partial(empty, empty, {}, {}) == {} and extends(empty, (), {}),
            'empty partial descent and extension')
    # The same unique empty system instantiates both T=d and T=O, and W_T.
    # A function from a nonempty D to empty O cannot exist; no such case is
    # admitted as a surjective exact quotient system.
    return len(partials)


def negative_controls():
    d, c = (ColouredSet(product(range(2), repeat=2)) for _ in range(2))
    o = ColouredSet([(0,), (1,)])
    full = tuple(product(range(2), repeat=3))
    do, co = ({p: p[:1] for p in s.points} for s in (d, c))
    g_d = d.permutation({p: (p[0], p[1] ^ 1) for p in d.points})
    h_c = c.permutation({p: p for p in c.points})
    require(g_d in d.automorphisms() and h_c in c.automorphisms()
            and induced(d, o, do, g_d) == induced(c, o, co, h_c),
            'd-only flip and C identity are actual compatible coordinate automorphisms')
    sparse = {x for x in full if x[1] == x[2]}
    require({x[:2] for x in sparse} == set(d.points)
            and {(x[0], x[2]) for x in sparse} == set(c.points),
            'nonfull subset still projects onto both coordinate sets')
    flip_d = lambda x: (x[0], x[1] ^ 1, x[2])
    require({flip_d(x) for x in sparse} != sparse,
            'compatible d-only flip does not preserve the nonfull subset')

    def extra_colour(x, y):
        relation = x[1] == y[2] and x[2] == y[1]
        return difference(x, y), relation

    extra = ColouredSet(full, extra_colour)
    x, y = (0, 0, 0), (1, 0, 0)
    require(difference(x[:2], y[:2]) == difference(flip_d(x)[:2], flip_d(y)[:2])
            and difference((x[0], x[2]), (y[0], y[2]))
            == difference((flip_d(x)[0], flip_d(x)[2]), (flip_d(y)[0], flip_d(y)[2])),
            'the compatible coordinate automorphisms preserve both coordinate colours')
    require(extra_colour(x, y) != extra_colour(flip_d(x), flip_d(y)),
            'extra relation is not reconstructed by those coordinate colours')
    require(not extra.preserves({p: flip_d(p) for p in full})
            and len(extra.automorphisms()) == 4,
            'full arbitrary coloured product has only four actual automorphisms')

    # Explicit finite action model with the C premise removed: o can move,
    # but c is fixed.  Even surjectivity onto Aut(O) does not repair this.
    ad = d.automorphisms()
    ac_bad = tuple(c.permutation({p: (p[0] ^ shift, p[1]) for p in c.points})
                   for shift in range(2))
    require({induced(c, o, co, h) for h in ac_bad} == set(o.automorphisms()),
            'bad C action still surjects onto owner automorphisms')
    w = ColouredSet(full)
    bad_action = []
    for g, h in product(ad, ac_bad):
        if induced(d, o, do, g) == induced(c, o, co, h):
            bad_action.append(w.permutation({p: (d.image(g, p[:2])[0],
                                                d.image(g, p[:2])[1],
                                                c.image(h, (p[0], p[2]))[1]) for p in full}))
    t = ColouredSet([(0,), (1,)])
    check_prescribed_lifting(d, t, {p: p[1:] for p in d.points}, ad, t.automorphisms())
    require(tuple(range(len(full))) in bad_action
            and all(tuple(g[h[i]] for i in range(len(full))) in bad_action
                    for g, h in product(bad_action, repeat=2)),
            'bad product permutations form an explicit finite action group')
    wt = {p: p[1:2] for p in full}
    images = {g: induced(w, t, wt, g) for g in bad_action}
    kernel = [g for g in bad_action if images[g] == (0, 1)]
    require(len(bad_action) == 4 and len(kernel) == 2
            and set(images.values()) == set(t.automorphisms()),
            'bad product action is still onto T with a two-element kernel')
    x, y = (0, 0, 0), (0, 0, 1)
    require(wt[x] == wt[y] and not any(w.image(g, x) == y for g in kernel),
            'without C prescribed-point/fibre-transitive premise kernel conclusion fails')
    require(not any(c.image(h, (0, 0)) == (0, 1) for h in ac_bad),
            'identity owner request on C cannot prescribe this point image')
    return len(sparse), len(extra.automorphisms()), len(kernel)


def nonsplit_controls():
    # Regular C4 action, quotient parity C2; this is an action example,
    # without claiming that an uncoloured four-cycle has automorphism C4.
    points, group, quotient = tuple(range(4)), tuple(range(4)), tuple(range(2))
    add = lambda a, b: (a + b) % 4
    act = lambda g, x: (g + x) % 4
    require(all(add(add(a, b), c) == add(a, add(b, c)) for a, b, c in product(group, repeat=3)),
            'C4 group law is associative')
    require(all(add(0, a) == add(a, 0) ==  a and add(a, -a % 4) == 0 for a in group),
            'C4 identity and inverses')
    require(all(act(add(a, b), x) == act(a, act(b, x)) for a, b, x in product(group, group, points)),
            'regular action respects group law')
    require(all(add(a, b) % 2 == (a % 2 + b % 2) % 2 for a, b in product(group, repeat=2)),
            'parity is a surjective group homomorphism')
    sections = [(0, odd) for odd in (1, 3)]
    require(not any(all(section[(a + b) % 2] == add(section[a], section[b])
                        for a, b in product(quotient, repeat=2)) for section in sections),
            'neither possible identity-preserving parity section is a group section')
    requests = 0
    for x, y, eta in product(points, points, quotient):
        if (x % 2 + eta) % 2 == y % 2:
            require(any(g % 2 == eta and act(g, x) == y for g in group),
                    'nonsplit quotient still has every prescribed-action point lift')
            requests += 1
        if x % 2 == y % 2:
            require(any(act(g, x) == y for g in (0, 2)), 'nonsplit quotient kernel is fibre transitive')
    require(requests == 16, 'all sixteen compatible nonsplit point requests checked')
    return requests, len(sections)


def finite_base_controls():
    """Literal finite-base restriction, with a supplied finite ambient witness.

    Three two-point equivalence classes have 48 actual colour automorphisms.
    Taking C=X supplies a concrete witness here; it is not an infinite EPPA
    provider or an assertion that arbitrary compatible owners always lift.
    """
    ambient = ColouredSet(product(range(3), range(2)), equivalence_colour)
    ambient_owners = ColouredSet([(i,) for i in range(3)], lambda x, y: x == y)
    quotient = {x: x[:1] for x in ambient.points}
    actions = ambient.automorphisms()
    require(len(actions) == 48, 'pure-equivalence six-point actual colour group has order 48')
    owner_actions = {g: induced(ambient, ambient_owners, quotient, g) for g in actions}
    reports = []
    for base_values, include_requests in (((0, 1), True), ((), True),
                                          ((0, 1), False), ((), False)):
        base = ColouredSet([(i,) for i in base_values], lambda x, y: x == y)
        seed = {(i, 0) for i in base_values}
        original = tuple(sorted(seed))
        requests = []
        if include_requests:
            for partial in partial_isometries(ambient, original):
                for gamma in base.automorphisms():
                    if not all(base.image(gamma, quotient[x]) == quotient[y]
                               for x, y in partial.items()):
                        continue
                    candidates = [g for g in actions if extends(ambient, g, partial)
                                  and all(ambient_owners.image(owner_actions[g], b)
                                          == base.image(gamma, b) for b in base.points)]
                    require(candidates, 'compatible request has a simultaneous actual ambient lift')
                    # Empty requests can move both seed representatives to
                    # their partners, so A* genuinely enlarges the seed.
                    lift = max(candidates, key=lambda g: len(
                        {ambient.image(g, x) for x in seed} - seed))
                    requests.append((partial, gamma, lift))
        enlarged = seed | {ambient.image(g, x) for _, _, g in requests for x in seed}
        require(all(quotient[x] in base.points for x in enlarged), 'A* stays over B')
        c = ambient
        require(enlarged <= set(c.points), 'the concrete witness C contains A*')
        for partial in partial_isometries(c, tuple(sorted(enlarged))):
            require(any(extends(c, g, partial) for g in actions),
                    'this concrete C extends every partial isometry of A*')
        w = ColouredSet([x for x in c.points if quotient[x] in base.points], equivalence_colour)
        projection = {x: quotient[x] for x in w.points}
        require(seed <= set(w.points) and set(projection.values()) == set(base.points),
                'restricted W contains original seed and projects onto the entire B')
        restricted_actions = w.automorphisms()
        for partial, gamma, lift in requests:
            beta = lift  # An actual Aut(C) extending the entire lift|S.
            seed_partial = {x: ambient.image(lift, x) for x in seed}
            require(extends(c, beta, seed_partial), 'beta extends the chosen map on all of S')
            image = {x: c.image(beta, x) for x in w.points}
            require(set(image.values()) == set(w.points), 'beta restricts to a permutation of W')
            restricted = w.permutation(image)
            require(restricted in restricted_actions and w.preserves(image),
                    'beta restriction is an actual colour automorphism of W')
            require(extends(w, restricted, partial)
                    and induced(w, base, projection, restricted) == gamma,
                    'restriction preserves original p and prescribed gamma on ENTIRE B')
            for x in w.points:
                representative = (x[0], 0)
                require(quotient[c.image(beta, x)] == quotient[c.image(beta, representative)]
                        == base.image(gamma, quotient[x]),
                        'representatives force the full owner component of the restriction')
        if not base_values:
            require(not seed and not enlarged and not w.points
                    and restricted_actions == ((),), 'empty base gives empty W and its trivial group')
            require(len(requests) == int(include_requests),
                    'empty base has exactly one compatible empty request, or no chosen requests')
        if not include_requests:
            require(not requests and enlarged == seed, 'no requirements leaves A*=S')
        if base_values and include_requests:
            require(len(requests) == 8 and len(enlarged) == 4,
                    'all eight compatible requests, including both empty owner actions, enlarge A* to four points')
        reports.append(len(requests))
    require(reports == [8, 1, 0, 0], 'finite-base request counts include both empty and no-request boundaries')
    return len(actions), tuple(reports)


def seed_conjugation_controls():
    """Finite group control for the prescribed-owner seed-conjugation lemma."""
    w = ColouredSet(product(range(2), repeat=2), equivalence_colour)
    owners = ColouredSet([(0,), (1,)], lambda x, y: x == y)
    projection = {x: x[:1] for x in w.points}
    actions, owner_group = w.automorphisms(), owners.automorphisms()
    components = {g: induced(w, owners, projection, g) for g in actions}
    require(len(actions) == 8 and set(components.values()) == set(owner_group),
            'four-point wreath action has order eight and the full owner action')
    require(all(compose(g, h) in actions
                and components[compose(g, h)] == compose(components[g], components[h])
                for g, h in product(actions, repeat=2)), 'owner component is a group homomorphism')
    seed = {(0, 0), (1, 0)}
    orbits = {frozenset(w.image(g, x) for g in actions) for x in w.points}
    require(all(orbit & seed for orbit in orbits), 'nonempty A0 meets every group orbit')
    moves = {x: tuple(g for g in actions if w.image(g, x) in seed) for x in w.points}
    require(all(moves.values()), 'every point can move into original A0')
    singleton_lifts = {}
    for a, b, delta in product(sorted(seed), sorted(seed), owner_group):
        if owners.image(delta, projection[a]) == projection[b]:
            singleton_lifts[a, b, delta] = tuple(g for g in actions
                                                if w.image(g, a) == b and components[g] == delta)
            require(singleton_lifts[a, b, delta], 'every compatible original singleton request lifts exactly')
    point_requests = conjugations = 0
    for x, y, gamma in product(w.points, w.points, owner_group):
        if owners.image(gamma, projection[x]) != projection[y]:
            continue
        point_requests += 1
        for g, h in product(moves[x], moves[y]):
            a, b = w.image(g, x), w.image(h, y)
            delta = compose(compose(components[h], gamma), inverse(components[g]))
            require(owners.image(delta, projection[a]) == projection[b],
                    'h_owner gamma g_owner^-1 is the compatible seed component')
            for k in singleton_lifts[a, b, delta]:
                result = compose(compose(inverse(h), k), g)
                require(result in actions and w.image(result, x) == y
                        and components[result] == gamma,
                        'h^-1 k g sends x to y with the EXACT prescribed owner component')
                conjugations += 1
    require((len(singleton_lifts), point_requests, conjugations) == (4, 16, 512),
            'exhaustive seed and conjugation request counts')
    return len(singleton_lifts), point_requests, conjugations


def orbit_trim_controls():
    """Finite invariant-partition interface, not greatest-F or source-provider evidence."""
    points = tuple(product(range(3), range(2)))
    packets = {frozenset((i, bit) for bit in range(2)) for i in range(3)}
    actions = tuple({x: ((x[0] + shift) % 3, x[1]) for x in points} for shift in range(3))
    require(all(frozenset(g[x] for x in packet) in packets
                for g, packet in product(actions, packets)), 'cyclic group preserves the packet partition')
    seed = frozenset([(0, 0), (0, 1)])
    translates = {frozenset(g[x] for x in seed) for g in actions}
    trimmed = frozenset().union(*translates)
    require(translates == packets and trimmed == frozenset(points),
            'orbit of one full packet is a union of full packets')
    require(all(frozenset(g[x] for x in trimmed) == trimmed for g in actions),
            'orbit trim is group invariant')
    require(all(any(g[x] in seed for g in actions) for x in trimmed),
            'every retained point moves back into the original full-packet seed')
    incomplete = frozenset([(0, 0)])
    incomplete_trim = frozenset(g[x] for g in actions for x in incomplete)
    require(len(incomplete_trim) == 3 and all(incomplete_trim & packet
                                             and not packet <= incomplete_trim for packet in packets),
            'an incomplete-packet seed can have invariant orbit union that is not full-packet closed')
    return len(trimmed), len(packets), len(incomplete_trim)


def main():
    nonnested, owner, nested, sources, partials, extensions, c_requests = positive_controls()
    empty = empty_controls()
    sparse, extra_aut, bad_kernel = negative_controls()
    nonsplit, sections = nonsplit_controls()
    ambient_aut, finite_base_counts = finite_base_controls()
    singleton_requests, transferred_requests, conjugations = seed_conjugation_controls()
    trimmed_points, packets, incomplete_points = orbit_trim_controls()
    print('Owner-action finite controls passed: actual F2^3 colour groups W/D/C/O = 8/4/4/2; '
          f'nonnested W->d kernel {nonnested[0]} ({nonnested[1]} prescribed point requests), '
          f'nested W->O kernel {owner[0]} ({owner[1]} requests), '
          f'W->W_T=C kernel {nested[0]} ({nested[1]} requests); '
          f'{sources} sparse sources, {partials} partial isometries, '
          f'{extensions} chosen-D/exact-owner extension requests, {c_requests} prescribed C requests; '
          f'empty system: trivial groups and {empty} empty partial isometry; '
          f'negative controls: {sparse}-point nonfull subset, extra relation with {extra_aut} automorphisms, '
          f'nontransitive {bad_kernel}-element kernel after dropping C premise; '
          f'nonsplit C4->C2: {nonsplit} point lifts and {sections} rejected candidate sections. '
          f'Finite-base restriction: {ambient_aut} actual ambient automorphisms, '
          f'{finite_base_counts} requests in nonempty/empty/no-request boundary cases; '
          f'seed conjugation: {singleton_requests} singleton requests, {transferred_requests} arbitrary-point requests, '
          f'{conjugations} exact-component h^-1 k g checks; '
          f'finite partition orbit trim: {trimmed_points} points/{packets} full packets, '
          f'{incomplete_points}-point incomplete-seed negative control. '
          'No CCO, arbitrary EPPA, infinite-provider, or master-theorem certification.')


if __name__ == '__main__':
    main()
