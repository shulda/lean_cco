#!/usr/bin/env python3
"""Independent bounded finite controls for the full-owner transversal arguments.

This script imports no other control script and does not inspect TeX text.
The packet models are M = {0,1,2} x F2^d, d <= 2, for EVERY subgroup H.
Within a packet every difference is named; between packets only its H-coset
is named.  Owners are G/H.  The represented action consists of packet
permutations, independent H-shifts, and one global G/H shift.  It is checked
as a structured permutation group, not obtained by enumerating 12! maps.

These are finite group-action, matrix, and constraint diagnostics.  Finite
orbits are never called algebraic-closure evidence.  No finite model here
certifies the infinite source, semantic CCO, SAP, primitivity, an HKN output,
EPPA, or the hypotheses of any theorem.  In particular the separate raw
Cayley-table diagnostic deliberately includes proper finite equivalences.
"""
from collections import Counter
from itertools import combinations, permutations, product


def require(condition, message):
    if not condition:
        raise AssertionError(message)


def subsets(values):
    values = tuple(values)
    for size in range(len(values) + 1):
        yield from combinations(values, size)


def subgroups(dimension):
    """All subgroups, tested by the actual XOR operation, including 0 and G."""
    group = tuple(range(1 << dimension))
    return tuple(frozenset(s) for s in subsets(group)
                 if 0 in s and all(x ^ y in s for x, y in product(s, repeat=2)))


class PacketModel:
    def __init__(self, dimension, subgroup, packets=3):
        self.g = tuple(range(1 << dimension))
        self.h = subgroup
        self.n = packets
        self._cosets = tuple(min(value ^ h for h in subgroup) for value in self.g)
        self.points = tuple(product(range(packets), self.g))
        self.index = {x: i for i, x in enumerate(self.points)}
        self.owners = tuple(sorted({self.coset(x) for x in self.g}))

    def coset(self, value):
        return self._cosets[value]

    def owner(self, point):
        return self.coset(point[1])

    def colour(self, x, y):
        if x[0] == y[0]:
            return 'thin', x[1] ^ y[1]
        return 'outside', self.coset(x[1] ^ y[1])

    @staticmethod
    def translate(point, shift):
        return point[0], point[1] ^ shift

    def transport(self, colour, shift):
        kind, value = colour
        return kind, value ^ shift if kind == 'thin' else self.coset(value ^ shift)

    def preserves(self, mapping):
        return (len(set(mapping.values())) == len(mapping)
                and all(self.colour(x, y) == self.colour(mapping[x], mapping[y])
                        for x, y in product(mapping, repeat=2)))

    def represented_actions(self):
        for perm in permutations(range(self.n)):
            for offsets in product(sorted(self.h), repeat=self.n):
                for global_shift in self.owners:
                    yield tuple((perm[i], value ^ offsets[i] ^ global_shift)
                                for i, value in self.points)


def action_controls(model, counts):
    actions = tuple(model.represented_actions())
    require(len(set(actions)) == len(actions), 'structured normal forms are unique')
    expected = len(tuple(permutations(range(model.n)))) * len(model.h) ** model.n * len(model.owners)
    require(len(actions) == expected, 'represented action cardinality')
    action_set = set(actions)
    generators = []
    identity = model.points
    # Check the represented group using closure under a generating set, rather
    # than a quadratic all-pairs multiplication loop or all carrier bijections.
    for i in range(1, model.n):
        generators.append(tuple((i if p == 0 else 0 if p == i else p, g)
                                for p, g in model.points))
    for i, h in product(range(model.n), sorted(model.h)):
        generators.append(tuple((p, g ^ h if p == i else g) for p, g in model.points))
    generators.extend(tuple((p, g ^ shift) for p, g in model.points) for shift in model.owners)
    require(identity in action_set, 'represented group contains identity')
    for action in actions:
        mapping = dict(zip(model.points, action))
        require(model.preserves(mapping), 'represented action preserves every literal fine colour')
        owner_shift = model.coset(mapping[(0, 0)][1])
        for point, shift in product(model.points, model.g):
            require(mapping[model.translate(point, shift)]
                    == model.translate(mapping[point], shift), 'all named packet functions commute')
            require(model.owner(mapping[point]) == model.coset(model.owner(point) ^ owner_shift),
                    'one global owner language action, literal raw names fixed')
            counts['action_function_checks'] += 1
        for generator in generators:
            composite = tuple(generator[model.index[y]] for y in action)
            require(composite in action_set, 'represented set closed under each generator')
            counts['generator_compositions'] += 1
    for packet, owner in product(range(model.n), model.owners):
        fibre = {x for x in model.points if x[0] == packet and model.owner(x) == owner}
        require(len(fibre) == len(model.h), 'full packet owner fibre has size |H|')
        counts['packet_owner_fibres'] += 1
    for point in model.points:
        thin_orbit = {model.translate(point, g) for g in model.g}
        require(len(thin_orbit) == len(model.g), 'G acts regularly on each real packet')
        stabilizer = {g for g in model.g
                      if model.owner(model.translate(point, g)) == model.owner(point)}
        require(stabilizer == model.h, 'owner stabilizer is exactly H, possibly nontrivial')
        named_orbit = {a[model.index[point]] for a in actions
                       if model.owner(a[model.index[(0, 0)]]) == 0}
        require(named_orbit == {x for x in model.points if model.owner(x) == model.owner(point)},
                'represented owner-fixing orbit is the full finite owner fibre')
        counts['point_orbits'] += 1
    counts['nonfaithful_owner_models'] += int(len(model.h) > 1)
    counts['represented_actions'] += len(actions)
    return action_set


def origin_controls(model, actions, counts):
    """All origin gauges; all packet-permutation/phase-offset embedding candidates."""
    for origins in product(model.g, repeat=model.n):
        points = tuple(product(range(model.n), model.g))
        inflation = {x: (x[0], x[1] ^ origins[x[0]]) for x in points}
        require(len(set(inflation.values())) == len(points), 'origin inflation is bijective')
        for x, y in product(points, repeat=2):
            i, g = x
            j, h = y
            origin_colour = model.colour((i, origins[i]), (j, origins[j]))
            require(model.colour(inflation[x], inflation[y])
                    == model.transport(origin_colour, g ^ h), 'entire fine matrix inflation law')
            counts['inflated_fine_pairs'] += 1
        for x, g in product(points, model.g):
            require(inflation[model.translate(x, g)] == model.translate(inflation[x], g),
                    'inflation preserves every total packet function')
            require(model.owner(inflation[x]) == model.coset(origins[x[0]] ^ x[1]),
                    'inflated owner equals translated origin owner')
        # Rebase to zero origins: abstract coordinates change by origins[i].
        for x in points:
            rebased = (x[0], x[1] ^ origins[x[0]])
            require(inflation[x] == rebased, 'changing origins is a gauge change, not a section')
        counts['origin_gauges'] += 1
    for perm in permutations(range(model.n)):
        for offsets in product(model.g, repeat=model.n):
            mapping = {x: (perm[x[0]], x[1] ^ offsets[x[0]]) for x in model.points}
            fine = model.preserves(mapping)
            aligned = len({model.coset(g) for g in offsets}) == 1
            require(fine == aligned, 'fine full-packet embeddings have one aligned quotient phase')
            if fine:
                require(tuple(mapping[x] for x in model.points) in actions,
                        'every fine phase-aligned candidate is represented')
                owner_fixed = all(model.owner(mapping[x]) == model.owner(x) for x in model.points)
                require(owner_fixed == all(g in model.h for g in offsets),
                        'literal owner labels impose exactly the zero quotient phase')
                # A fixed-base alignment is explicit: compose with the inverse
                # of this represented isomorphism on the whole complete image.
                inverse = {y: x for x, y in mapping.items()}
                require(model.preserves(inverse), 'complete-image alignment is a fine isomorphism')
                for base_size in (0, 1, model.n):
                    base = [x for x in model.points if x[0] < base_size]
                    require(all(inverse[mapping[x]] == x for x in base),
                            'complete protected base restored after phase-aligned inflation')
                    counts['complete_base_alignments'] += 1
                counts['aligned_embeddings'] += 1
            counts['embedding_candidates'] += 1
    if len(model.owners) > 1:
        bad = next(g for g in model.g if g not in model.h)
        partial_phase = {x: model.translate(x, bad if x[0] == 0 else 0) for x in model.points}
        require(not model.preserves(partial_phase), 'unaligned packet phases fail a literal fine matrix')
        global_phase = {x: model.translate(x, bad) for x in model.points}
        require(model.preserves(global_phase)
                and any(model.owner(global_phase[x]) != model.owner(x) for x in model.points),
                'raw-colour preservation alone does not preserve named owners')
        counts['phase_negative_controls'] += 2


def collision_controls(model, counts):
    """Exhaust bounded records, literal homomorphisms, and complete protected bases.

    Three source packets have target packet indices in {0,1}, or the
    injective tuple (0,1,2); all G-valued origin phases are included.  There
    are six available target packets, so a fresh target is always available.
    The ambient witness for a move swaps the old and fresh target packets;
    ONLY the chosen source packet is then changed in q.
    """
    ambient = PacketModel((len(model.g) - 1).bit_length(), model.h, packets=6)
    witnessed_swaps = set()
    for old, fresh in combinations(range(6), 2):
        mapping = {x: (fresh if x[0] == old else old if x[0] == fresh else x[0], x[1])
                   for x in ambient.points}
        require(ambient.preserves(mapping), 'ambient transposition preserves every actual fine colour')
        for x, g in product(ambient.points, ambient.g):
            require(ambient.owner(mapping[x]) == ambient.owner(x)
                    and mapping[ambient.translate(x, g)] == ambient.translate(mapping[x], g),
                    'ambient transposition fixes owners and commutes with all packet functions')
        witnessed_swaps.add(frozenset((old, fresh)))
        counts['ambient_swap_witnesses'] += 1
    pairs = tuple(combinations(range(3), 2))
    targets = tuple(product(range(2), repeat=3)) + ((0, 1, 2),)
    for records in subsets(pairs):
        records = frozenset(records)
        for initial in targets:
            if any(initial[i] == initial[j] for i, j in records):
                continue  # Recorded outside-F matrices forbid precisely these collisions.
            for base in subsets(range(3)):
                base = frozenset(base)
                if not all(pair in records for pair in combinations(sorted(base), 2)):
                    continue
                if len({initial[i] for i in base}) != len(base):
                    continue
                for phases in product(model.g, repeat=3):
                    current = list(initial)
                    protected = {i: (current[i], phases[i]) for i in base}

                    def verify():
                        for i in range(3):
                            for g, h in product(model.g, repeat=2):
                                x, y = (current[i], phases[i] ^ g), (current[i], phases[i] ^ h)
                                require(model.translate(x, h) == (current[i], phases[i] ^ g ^ h),
                                        'q preserves the literal total function t_h')
                                require(model.colour(x, y) == ('thin', g ^ h),
                                        'q is injective on each literal regular packet')
                                require(model.owner(x) == model.coset(phases[i] ^ g),
                                        'all literal owner labels survive packet move')
                        for i, j in records:
                            for g, h in product(model.g, repeat=2):
                                actual = model.colour((current[i], phases[i] ^ g),
                                                      (current[j], phases[j] ^ h))
                                require(actual == ('outside', model.coset(phases[i] ^ phases[j] ^ g ^ h)),
                                        'every recorded full matrix survives')
                        require(all((current[i], phases[i]) == point for i, point in protected.items()),
                                'complete protected base kept literally fixed')

                    verify()
                    while len(set(current)) < 3:
                        old_collisions = sum(current[i] == current[j] for i, j in pairs)
                        moving = next(i for i in range(3) if i not in base
                                      and any(i != j and current[i] == current[j] for j in range(3)))
                        neighbours = {j for j in range(3)
                                      if tuple(sorted((moving, j))) in records}
                        fixed_packets = {current[j] for j in neighbours}
                        old = current[moving]
                        require(old not in fixed_packets, 'recorded-neighbour closure excludes moving packet')
                        fresh = next(i for i in range(6) if i not in current)
                        before = tuple(current)
                        require(frozenset((old, fresh)) in witnessed_swaps,
                                'the selected local move has an actual finite ambient automorphism witness')
                        # The swap is an actual owner-preserving automorphism of
                        # the six-packet model and fixes entire recorded neighbours.
                        swap = lambda p: fresh if p == old else old if p == fresh else p
                        require(all(swap(p) == p for p in fixed_packets),
                                'ambient move fixes exactly the required neighbour packets')
                        current[moving] = swap(old)
                        require(all(current[j] == before[j] for j in range(3) if j != moving),
                                'replace only ONE source packet, not the whole q-image')
                        require(sum(current[i] == current[j] for i, j in pairs) < old_collisions,
                                'collision count strictly decreases without a new collision')
                        verify()
                        counts['single_packet_moves'] += 1
                    require(len(set(current)) == 3, 'completed q separates all full packets')
                    counts['collision_inputs'] += 1
                    counts['nonempty_protected_inputs' if base else 'empty_protected_inputs'] += 1
    # A collision with an unrecorded protected packet is intentional.  Fixing
    # its point (or entire packet) in the AMBIENT move fixes the colliding
    # origin, making avoidance impossible.  Replacing only q(Pi) succeeds.
    old, fresh = (0, 0), (1, 0)
    require(old == (0, 0) and old != fresh, 'explicit unrecorded base collision')
    all_points = tuple(product(range(3), model.g))
    fixing_target = [a for a in model.represented_actions() if a[model.index[old]] == old]
    require(fixing_target and all(a[model.index[old]] != fresh for a in fixing_target),
            'false extra condition: fixing an unrecorded collision target prevents moving the origin')
    q = {('base', g): (0, g) for g in model.g}
    q.update({('moving', g): (1, g) for g in model.g})
    require(len(set(q.values())) == 2 * len(model.g)
            and all(q['base', g] == (0, g) for g in model.g),
            'local replacement resolves the collision while the base stays fixed')
    require(set(all_points) >= set(q.values()), 'negative witness has an actual finite target')
    counts['unrecorded_target_negative_controls'] += 1


def raw_primitivity_diagnostics(counts):
    """Actual finite Cayley colour tables, separate from any SAP assertion.

    E is a subgroup, H <= E is the distinguished thin support, and D ranges
    over ALL subsets of E minus H.  Check the algebraic raw-equivalence criterion
    using actual represented relational products, without asserting that
    proper supports are impossible in these finite actions.
    """
    for dimension in range(3):
        group = tuple(range(1 << dimension))
        groups = subgroups(dimension)
        for e, h in product(groups, repeat=2):
            if not h <= e:
                continue
            for support in subsets(sorted(e - h)):
                d = frozenset(support)
                hd = frozenset(g for g in h if frozenset(g ^ a for a in d) == d)
                require(0 in hd and all(g ^ k in hd for g, k in product(hd, repeat=2)),
                        'H_D is an actual subgroup stabilizer')
                dd = {a ^ b for a, b in product(d, repeat=2)}
                products_close = (dd - h <= d) and (dd & h <= hd)
                raw = hd | d | {0}
                relation = {(x, y) for x, y in product(group, repeat=2) if x ^ y in raw}
                transitive = all((x, z) in relation for x, y in relation
                                 for yy, z in relation if y == yy)
                require(products_close == transitive,
                        'thin/nonthin product gates exactly detect global RAW equivalence closure')
                require(all((x, x) in relation for x in group)
                        and all((y, x) in relation for x, y in relation), 'raw relation is reflexive/symmetric')
                require(all(x ^ y in e for x, y in relation), 'raw equivalence candidate lies in E')
                # Literal old-colour unions are globally invariant under every
                # translation; this is not a relation confined to a named sort.
                for g in group:
                    require({(x ^ g, y ^ g) for x, y in relation} == relation,
                            'raw relation invariant in the entire finite action')
                counts['raw_support_candidates'] += 1
                counts['raw_equivalence_accepts' if transitive else 'raw_equivalence_rejects'] += 1
                if d and transitive and raw < e:
                    counts['proper_finite_raw_equivalences'] += 1
    require(counts['proper_finite_raw_equivalences'] > 0,
            'finite diagnostic must not silently claim infinite-source primitivity')


def cap_controls(counts):
    """Cartesian rows/columns/phases, independent of the packet action model."""
    points = tuple(product(range(4), range(4), range(2)))

    def colour(x, y):
        return x[0] == y[0], x[1] == y[1], x[2] ^ y[2]

    def owner(x):
        return x[0], x[2]

    edges = ((0, 1), (1, 2), (2, 3), (0, 3))
    prescribed = tuple((i, 0) for i in range(4))
    completions = tuple(tuple((i, column[i], 0) for i in range(4))
                        for column in product(range(4), repeat=4))
    joint = {tuple(colour(xs[i], xs[j]) for i, j in edges) for xs in completions}
    individual = [set(pattern[i] for pattern in joint) for i in range(4)]
    b, d = (False, True, 0), (False, False, 0)
    require(all(spectrum == {b, d} for spectrum in individual), 'each owner-pair cap has both colours')
    independent = set(product(*individual))
    require(joint < independent and len(independent) == 16 and len(joint) == 12,
            'product of individual caps strictly exceeds joint spectrum')
    bad = (b, b, b, d)
    require(bad in independent and bad not in joint, 'three equalities and one inequality obstruct the four-cycle')
    for selected in subsets(range(4)):
        exists = any(all(pattern[i] == bad[i] for i in selected) for pattern in joint)
        require(exists == (len(selected) < 4), 'EVERY proper subfamily has a common prescribed-owner completion')
        counts['four_cycle_subfamilies'] += 1
    require(not any(all(tuple(sorted(pair)) in edges for pair in combinations(triple, 2))
                    for triple in combinations(range(4), 3)), 'the displayed obstruction has no specified triangle')
    for i, j in edges:
        cap = {colour(x, y) for x, y in product(points, repeat=2)
               if owner(x) == prescribed[i] and owner(y) == prescribed[j]}
        require(cap == {b, d}, 'individual capped spectra computed directly from actual points')
        counts['individual_caps'] += 1
    counts['joint_cap_patterns'] = len(joint)
    counts['independent_cap_patterns'] = len(independent)
    # All equivalence partitions on three formal vertices, not only one Id edge.
    partitions = []
    for labels in product(range(3), repeat=3):
        blocks = frozenset(frozenset(i for i in range(3) if labels[i] == value)
                           for value in set(labels))
        if blocks not in partitions:
            partitions.append(blocks)
    require(len(partitions) == 5, 'all five equality-identification partitions')
    owners = tuple(product(range(2), range(2)))
    for blocks, assignment in product(partitions, product(owners, repeat=3)):
        descends = all(len({assignment[i] for i in block}) == 1 for block in blocks)
        # The quotient has a real representative with column 0 exactly when
        # lambda is a function on the identified vertex classes.
        realisations = []
        for block in blocks:
            possible = {x for x in points if all(owner(x) == assignment[i] for i in block)}
            realisations.append(possible)
        require(descends == all(realisations), 'Id cap requires lambda to descend after identification')
        counts['identity_cap_assignments'] += 1
        counts['identity_cap_accepts' if descends else 'identity_cap_rejects'] += 1
    counts['four_cycle_negative_controls'] += 1


def main():
    counts = Counter()
    subgroup_counts = []
    for dimension in range(3):
        groups = subgroups(dimension)
        subgroup_counts.append(len(groups))
        for subgroup in groups:
            model = PacketModel(dimension, subgroup)
            actions = action_controls(model, counts)
            origin_controls(model, actions, counts)
            collision_controls(model, counts)
            counts['packet_models'] += 1
    require(subgroup_counts == [1, 2, 5], 'complete subgroup coverage for F2^0, F2^1, F2^2')
    raw_primitivity_diagnostics(counts)
    cap_controls(counts)
    print('Owner-transversal bounded finite controls passed.')
    print('Coverage: d=0,1,2; all subgroup counts 1,2,5; three-packet action models; '
          'collision target budget six packets; no enumeration of 12! carrier maps.')
    for key in sorted(counts):
        print(f'  {key}: {counts[key]}')
    print('Limits: represented structured group actions and bounded finite constraint/matrix checks only. '
          'No infinite-source, acl, CCO, SAP, primitivity, HKN, or EPPA certification; '
          'proper finite raw equivalences are retained as diagnostic controls.')


if __name__ == '__main__':
    main()
