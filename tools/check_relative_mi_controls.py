#!/usr/bin/env python3
"""Bounded B028 orbit-safe/relative-MI interface diagnostics, NOT EPPA proofs.

Preflight representation: G=C2 or C2^2 acts regularly on actual packet
points (i,g), but owner labels are G/H cosets (all subgroups H are tested).
One helper packet per owner orbit has fibre size |H|, including H!=0.
Fine cross colours have three G-orbits: safe, partly safe, unsafe. S has
one ENTIRE safe orbit and one partial orbit; S^G is exactly the entire
safe orbit. The typed triangle table is FREE, so these positive finite
palette/diagram tests do not reuse an invalid strong-safe premise.

One R07 decoder per model is fixed before ALL legal corrections. Actual
packets are (i,f), |I|<=3, |G|<=4, and points are (i,f,z). The C2 path
reservoir has a genuine structural flip into its source edge; the C2^2
hole reservoir has H={0,1}, hence nonfaithful owners. Products of nonempty
menus are full in these free typed tables; original exact menus are
singletons and Top. Record singletons and one actual greatest-PC family
are retained while every action is checked against the fixed fine-colour
matrix. The fixed decoder is not recomputed per correction.

Search: all subgroups of G (<=16 subsets), <=128 decoder vertices; 1,024
legal lifts in each of two fixed models, at most 9.5 million point-pair
colour comparisons; <=1,152 explicit unsafe clique transports plus triples;
<=255 padded-source subsets; 24*4^4=6,144 structured candidate automorphisms
of a 16-point trim model (not all 16! maps). Fixed labels; no redundant
colour relabeling. Cached literal colour matrices make expected runtime
<10 seconds. Pilot: timeout 10s. Full: SIGALRM and phase deadline 30s.
Failures carry finite witnesses; success prints one bounded JSON checkpoint.
Reproduce: timeout 10s python tools/check_relative_mi_controls.py > /tmp/b028-controls.json

No other control script is imported. Finite diagnostics do NOT prove actual
infinite source/closed-SAP/CCO, HKN, EPPA, ambient lifting or MI assembly.
The trim example is a finite group/image diagnostic, not the actual source
provider. No group section or coherent choice is inferred.
"""
from collections import Counter
from itertools import combinations, permutations, product
import hashlib
import json
import signal
import time

START = time.monotonic()
SAFE, PARTIAL, UNSAFE, THIN = 1, 2, 3, 4


def require(ok, message, witness=None):
    if not ok:
        raise AssertionError((message, witness))


def tick():
    require(time.monotonic() - START < 30, '30-second diagnostic deadline')


def subsets(items):
    items = tuple(items)
    for n in range(len(items) + 1):
        yield from combinations(items, n)


def all_subgroups(order):
    return tuple(frozenset(s) for s in subsets(range(order))
                 if 0 in s and all(a ^ b in s for a, b in product(s, repeat=2)))


def helper_controls(counts, witnesses):
    for order in (2, 4):
        for h in all_subgroups(order):
            coset = lambda a: min(a ^ b for b in h)
            cosets = tuple(sorted({coset(g) for g in range(order)}))
            owners = tuple(product(range(2), cosets))  # Two distinct owner orbits.
            helper = tuple((orbit, g) for orbit in range(2) for g in range(order))
            own = lambda x: (x[0], coset(x[1]))
            require({own(x) for x in helper} == set(owners), 'ONE packet per owner orbit covers every owner')
            for orbit in range(2):
                packet = tuple((orbit, g) for g in range(order))
                require(len(set(packet)) == order, 'real packet action remains regular')
                for owner in owners:
                    fibre = [x for x in packet if own(x) == owner]
                    require(len(fibre) == (len(h) if owner[0] == orbit else 0),
                            'actual owner fibre has stabilizer multiplicity', (order, tuple(h), owner))
                    counts['owner_stabilizer_multiplicities'] += 1
            if len(h) > 1:
                require(len({own(x) for x in helper}) < len(helper), 'nonfaithful owner action is not free')
                witnesses.setdefault('nonfaithful_owner_helper', {'group_order': order, 'stabilizer': tuple(sorted(h)),
                                                                 'owner_orbits': 2, 'helper_packets': 2})
                if len(h) < order:
                    witnesses.setdefault('proper_nonfaithful_owner_helper',
                                         {'group_order': order, 'stabilizer': tuple(sorted(h)),
                                          'owner_fibre_size': len(h), 'owner_orbit_size': order // len(h)})
                counts['nonfaithful_helper_models'] += 1
            old_packet_ids = {10, 11}
            require(not {x[0] for x in helper} & old_packet_ids, 'helper has genuinely disjoint packet indices')
            counts['helper_models'] += 1
    tick()


def palette_controls(counts, witnesses):
    for order in (2, 4):
        palette = tuple(product((SAFE, PARTIAL, UNSAFE), range(order)))
        s = frozenset((kind, g) for kind, g in palette if kind == SAFE or (kind, g) == (PARTIAL, 0))
        translate = lambda a, g: (a[0], a[1] ^ g)
        orbit_safe = frozenset(a for a in palette if all(translate(a, g) in s for g in range(order)))
        require(orbit_safe == frozenset((SAFE, g) for g in range(order)), 'orbit-safe closure is one full orbit')
        require(translate((PARTIAL, 0), 1) not in s, 'pure-owner covariance does not imply unilateral safety')
        for a in palette:
            matrix = tuple(translate(a, g ^ h) for g, h in product(range(order), repeat=2))
            require((a in orbit_safe) == all(c in s for c in matrix), 'S^G iff EVERY full-matrix entry is safe', a)
            for shift in range(order):
                require((translate(a, shift) in orbit_safe) == (a in orbit_safe), 'S^G is unilaterally invariant')
                counts['orbit_safe_translation_checks'] += 1
            counts['full_matrix_safety_equivalences'] += 1
        # Old source packets 0,1 have an unsafe old matrix; 2,3 are padding.
        origins = {(i, j): (UNSAFE, 0) if (i, j) == (0, 1) else (SAFE, (i ^ j) % order)
                   for i, j in combinations(range(4), 2)}
        for (i, j), a in origins.items():
            for g, h in product(range(order), repeat=2):
                colour = translate(a, g ^ h)
                if i >= 2 or j >= 2:
                    require(colour in s, 'EVERY new cross matrix, including padding-to-old, is safe', (i, j, g, h))
                    counts['padded_new_safe_matrix_entries'] += 1
                else:
                    require(colour not in s, 'old unsafe recorded matrix is unchanged')
        if order == 2:
            vertices = tuple(product(range(4), range(order)))
            def unsafe_pair(x, y):
                if x[0] == y[0]:
                    return True  # Thin diversity is outside S in this finite diagnostic.
                edge = tuple(sorted((x[0], y[0])))
                return translate(origins[edge], x[1] ^ y[1]) not in s
            for chosen in subsets(vertices):
                if not chosen or not all(unsafe_pair(x, y) for x, y in combinations(chosen, 2)):
                    continue
                if len({x[0] for x in chosen}) >= 2:
                    require(all(x[0] < 2 for x in chosen), 'multi-packet unsafe clique excludes EVERY padding packet')
                    counts['padding_excluded_unsafe_cliques'] += 1
        witnesses['pure_safe_not_unilateral_G' + str(order)] = {'safe_origin': (PARTIAL, 0),
                                                               'unsafe_translate': (PARTIAL, 1)}
    tick()


class RowModel:
    def __init__(self, n, order, subgroup, records, counts):
        self.n, self.order, self.h = n, order, frozenset(subgroup)
        self.cosets = tuple(min(g ^ h for h in self.h) for g in range(order))
        self.records = frozenset(tuple(sorted(e)) for e in records)
        self.rows = tuple(product(range(order), repeat=n))
        self.packets = tuple(product(range(n), self.rows))
        self.points = tuple((i, f, z) for i, f in self.packets for z in range(order))
        self.index = {x: k for k, x in enumerate(self.points)}
        top = frozenset(product((SAFE, PARTIAL, UNSAFE), self.h))
        # Literal free typed products, computed ONCE on actual packet indices.
        domains = {(p, q): frozenset({(UNSAFE, 0)}) if self.recorded(p[0], q[0]) else top
                   for p, q in permutations(self.packets, 2)}
        next_domains = {}
        for (p, q), d in domains.items():
            value = d
            for r in self.packets:
                if r != p and r != q:
                    # Every compatible nonempty product is Top in this FREE
                    # typed palette. No identity menu is adjoined.
                    product_profile = top if domains[p, r] and domains[r, q] else frozenset()
                    value &= product_profile
            next_domains[p, q] = value
        require(next_domains == domains and all(domains.values()), 'actual greatest-PC domains already stable and nonempty')
        self.domains = domains
        self.signature = self.domain_signature()
        counts['one_fixed_PC_runs'] += 1
        counts['actual_packet_PC_domains'] += len(domains)
        self.colours = tuple(tuple(self.colour(x, y) for y in self.points) for x in self.points)

    def coset(self, g):
        return self.cosets[g]

    def recorded(self, i, j):
        return i != j and tuple(sorted((i, j))) in self.records

    def domain_signature(self):
        return hashlib.sha256(repr(sorted((p, q, tuple(sorted(d))) for (p, q), d in self.domains.items())).encode()).hexdigest()

    def colour(self, x, y):
        i, f, z = x
        j, k, w = y
        if x == y:
            return -1  # Logical equality stays outside diversity colours.
        if (i, f) == (j, k):
            return THIN * self.order + (z ^ w)
        d = self.domains[(i, f), (j, k)]
        if self.recorded(i, j):
            require(d == {(UNSAFE, 0)}, 'record singleton retained in ONE fixed family')
            return UNSAFE * self.order + (z ^ w)
        # h^u((z+w)D)=u h(u(z+w)D); choose minimum group value
        # of the ACTUAL typed coset after moving its first endpoint.
        u = z ^ f[j] ^ w ^ k[i]
        phase = u ^ self.coset(u ^ z ^ w)
        require(self.coset(phase) == self.coset(z ^ w), 'decoded fine atom has the moved owner types')
        return SAFE * self.order + phase

    def legal_matrix(self, c):
        return all(c[i * self.n + j] == c[j * self.n + i]
                   for i, j in combinations(range(self.n), 2) if not self.recorded(i, j))

    def structural_actions(self):
        for sigma in permutations(range(self.n)):
            if any(self.recorded(i, j) != self.recorded(sigma[i], sigma[j])
                   for i, j in combinations(range(self.n), 2)):
                continue
            for b in product(range(self.order), repeat=self.n):
                if len({self.coset(x) for x in b}) != 1:
                    continue  # ONE global owner component.
                if any(b[i] != b[j] for i, j in self.records):
                    continue  # Every literal old origin colour is zero.
                yield sigma, b

    def image(self, x, sigma, b, c):
        i, f, z = x
        new = [None] * self.n
        for j in range(self.n):
            new[sigma[j]] = f[j] ^ c[i * self.n + j] ^ b[i]
        return sigma[i], tuple(new), z ^ b[i]


def row_controls(counts, witnesses):
    models = (RowModel(3, 2, (0, 1), ((0, 1), (1, 2)), counts),
              RowModel(2, 4, (0, 1), (), counts))
    for model in models:
        n, order = model.n, model.order
        pairs = tuple(combinations(range(len(model.points)), 2))
        matrices = tuple(c for c in product(range(order), repeat=n * n) if model.legal_matrix(c))
        for sigma, b in model.structural_actions():
            for c in matrices:
                image = tuple(model.index[model.image(x, sigma, b, c)] for x in model.points)
                require(len(set(image)) == len(image), 'full-row lift is a literal point bijection', (n, order, sigma, b, c))
                require(all(model.colours[image[x]][image[y]] == model.colours[x][y] for x, y in pairs),
                        'ALL legal row corrections preserve ONE preselected fine decoder', (n, order, sigma, b, c))
                require(all(model.coset(model.points[image[x]][2])
                            == model.coset(model.points[x][2] ^ b[0]) for x in range(len(image))),
                        'whole owner component is global even with nonfaithful stabilizers')
                counts['universal_fixed_decoder_lifts'] += 1
                counts['literal_fine_pair_comparisons'] += len(pairs)
        require(model.signature == model.domain_signature(), 'PC family was not recomputed for any later correction')
        for x, y in combinations(model.points, 2):
            if x[:2] == y[:2]:
                continue
            code = model.colour(x, y)
            if not model.recorded(x[0], y[0]):
                require(code // order == SAFE, 'EVERY unrecorded actual-packet matrix is safe')
                if x[0] == y[0]:
                    counts['same_index_distinct_row_safe_pairs'] += 1
                for g, h in product(range(order), repeat=2):
                    require((code ^ g ^ h) // order == SAFE, 'every further endpoint translation remains ORIGINAL S-safe')
                    counts['safe_full_matrix_translates'] += 1
            else:
                require(code == UNSAFE * order + (x[2] ^ y[2]), 'old recorded matrix never recoloured')
        witnesses['fixed_decoder_G' + str(order)] = {'vertices': len(model.points), 'actual_packets': len(model.packets),
                                                    'PC_signature': model.signature, 'legal_corrections': len(matrices),
                                                    'owner_stabilizer': tuple(sorted(model.h)),
                                                    'owner_labels': tuple(sorted(set(model.cosets)))}
        tick()
    # Unsafe-clique descent in the genuine three-index path reservoir.
    model = models[0]
    for chosen in combinations(model.points, 3):
        if not all(model.colour(x, y) // 2 != SAFE for x, y in combinations(chosen, 2)):
            continue
        packets = {x[:2] for x in chosen}
        if len(packets) >= 2:
            indices = {p[0] for p in packets}
            require(len(indices) == len(packets), 'unsafe clique cannot use two rows at the SAME structural index')
            require(all(model.recorded(i, j) for i, j in combinations(indices, 2)),
                    'unsafe clique projects to a RECORDED structural clique')
            counts['unsafe_triangle_projection_tests'] += 1
    for i, j in sorted(model.records):
        for f, k in product(model.rows, repeat=2):
            union = tuple((i, f, z) for z in range(2)) + tuple((j, k, z) for z in range(2))
            for chosen in subsets(union):
                if not chosen or {x[0] for x in chosen} != {i, j}:
                    continue
                require(all(model.colour(x, y) // 2 != SAFE for x, y in combinations(chosen, 2)),
                        'selected full-packet subset is genuinely unsafe')
                sigma = (0, 1, 2) if (i, j) == (0, 1) else (2, 1, 0)
                b, c = (0, 0, 0), [0] * 9
                forced = {i: f, j: k}
                for a, row in forced.items():
                    for column in range(3):
                        c[3 * a + column] = row[column]
                # At most one end of the unrecorded 0--2 pair is touched.
                if 0 in forced:
                    c[6] = c[2]
                elif 2 in forced:
                    c[2] = c[6]
                c = tuple(c)
                require(model.legal_matrix(c), 'one simultaneous clique-zeroing matrix is legal')
                target = tuple(model.image(x, sigma, b, c) for x in chosen)
                require(all(x[0] in (0, 1) and x[1] == (0, 0, 0) for x in target),
                        'ONE structural flip plus ONE correction sends clique into old source zero rows')
                require(all(model.colour(x, y) == model.colour(ax, ay)
                            for (x, ax), (y, ay) in combinations(tuple(zip(chosen, target)), 2)),
                        'unsafe clique remains unsafe in SAME decoded structure')
                if any(any(row) for row in forced.values()):
                    moved_old_zeros = tuple(model.image((a, (0, 0, 0), 0), sigma, b, c)
                                            for a in forced)
                    require(any(x[1] != (0, 0, 0) for x in moved_old_zeros),
                            'clique correction need NOT fix separately prescribed old zero-row packets')
                    witnesses.setdefault('clique_zeroing_moves_old_zero_rows',
                                         {'touched': tuple(sorted(forced)),
                                          'selected_rows': tuple(forced[a] for a in sorted(forced)),
                                          'images_of_old_zero_rows': moved_old_zeros})
                    counts['clique_zeroing_without_source_zero_fix'] += 1
                counts['unsafe_multipacket_zeroings'] += 1
    tick()


def trim_colour(x, y):
    if x == y:
        return 'equality',
    if x[0] == y[0]:
        return 'thin', x[1] ^ y[1]
    return 'outside', x[0] // 2 == y[0] // 2, (x[1] ^ y[1]) & 2


def trim_controls(counts, witnesses):
    points = tuple(product(range(4), range(4)))
    index = {x: i for i, x in enumerate(points)}
    own = lambda x: (x[0] // 2, x[1] & 2)
    owner_labels = frozenset(map(own, points))
    coarse = lambda x: x[1] & 2
    pairs = tuple(combinations(points, 2))
    full_aut, image_group = [], []
    # Named thin colours force every packet bijection to be a translation;
    # this finite normal form exhausts candidates without searching 16!.
    for sigma in permutations(range(4)):
        for offsets in product(range(4), repeat=4):
            mapping = {x: (sigma[x[0]], x[1] ^ offsets[x[0]]) for x in points}
            if not all(trim_colour(x, y) == trim_colour(mapping[x], mapping[y]) for x, y in pairs):
                continue
            underlying = tuple(index[mapping[x]] for x in points)
            full_aut.append(underlying)
            components = tuple(delta for delta in (0, 2)
                               if all(own(mapping[x]) == (own(x)[0], own(x)[1] ^ delta) for x in points))
            require(len(components) <= 1, 'full owner support makes language component RECOVERABLE')
            if components:
                image_group.append((components[0], underlying))
    require(len(full_aut) == 256 and len(image_group) == 128, 'semilinear IMAGE is proper in FULL original Aut')
    require({delta for delta, _ in image_group} == {0, 2}, 'whole coarse owner action is onto')
    counts['structured_trim_automorphism_candidates'] = 24 * 4 ** 4
    counts['full_original_trim_automorphisms'] = len(full_aut)
    counts['semilinear_image_automorphisms'] = len(image_group)
    a0 = {(0, 0)}
    full_a0 = {x for x in points if x[0] == 0}
    trimmed = {points[action[index[x]]] for _, action in image_group for x in full_a0}
    require(trimmed == {x for x in points if x[0] in (0, 1)}, 'orbit trim is a union of WHOLE real packets')
    require({coarse(x) for x in trimmed} == {0, 2}, 'EXACT coarse B support survives trim')
    require({own(x) for x in trimmed} < owner_labels, 'full fine U support need NOT survive trim')
    for _, action in image_group:
        require({points[action[index[x]]] for x in trimmed} == trimmed, 'same orbit trim invariant under ENTIRE K')
        counts['trim_invariance_actions'] += 1
    for packet in (0, 1):
        for zset in subsets(tuple((packet, g) for g in range(4))):
            if not zset:
                continue
            for selected in zset:
                # Bring its packet into F[A0], then ONE GLOBAL translation.
                delta = lambda x: (0 if x[0] == packet else packet if x[0] == 0 else x[0], x[1])
                shift = delta(selected)[1]
                alpha = lambda x: (delta(x)[0], delta(x)[1] ^ shift)
                whole = tuple(index[alpha(x)] for x in points)
                require(any(action == whole for _, action in image_group), 'selected-root correction belongs to K')
                require({alpha(x) for x in zset} <= full_a0 and alpha(selected) in a0,
                        'single-packet trim transport keeps clique and chosen root')
                if coarse(selected) != coarse(alpha(selected)):
                    witnesses.setdefault('root_correction_changes_owner', {'selected': selected,
                                                                           'image': alpha(selected), 'global_shift': shift})
                    counts['root_corrections_allowed_owner_change'] += 1
                counts['single_packet_selected_root_transports'] += 1
    # Multi-packet version only assumes a supplied transport into F[A0].
    # Here F[A0]=trimmed for A0 having one chosen point in each old packet.
    a1 = {(0, 0), (1, 1)}
    for chosen in subsets(tuple(sorted(trimmed))):
        if not chosen:
            continue
        for selected in chosen:
            target = next(a for a in a1 if a[0] == selected[0])
            shift = selected[1] ^ target[1]
            translated = {(i, g ^ shift) for i, g in chosen}
            require(translated <= trimmed and (selected[0], selected[1] ^ shift) in a1,
                    'ONE global thin shift corrects a selected root without losing any packet')
            counts['multipacket_selected_root_corrections'] += 1
    # If only one of three owner labels is realised, two language permutations
    # have the same identity vertex map. This is different from G's kernel.
    gamma3 = tuple(permutations(range(3)))
    require(sum(g[0] == 0 for g in gamma3) == 2, 'missing fine support can destroy forgetful injectivity')
    counts['negative_missing_fine_support'] += 1
    witnesses['trim_support'] = {'fine_U_before': tuple(sorted(owner_labels)),
                                 'fine_U_after': tuple(sorted({own(x) for x in trimmed})),
                                 'coarse_B_after': tuple(sorted({coarse(x) for x in trimmed})),
                                 'K_image': len(image_group), 'full_original_Aut': len(full_aut)}
    tick()


def request_controls(counts, witnesses):
    gamma = tuple(permutations(range(3)))
    real_points = tuple(product(range(3), range(2)))
    a0 = (0, 0)
    # Empty requests retain ENTIRE Gamma_B, not just an induced partial map.
    for prescribed in gamma:
        extension = {x: (prescribed[x[0]], x[1]) for x in real_points}
        require(len(set(extension.values())) == len(real_points), 'empty request has a full finite owner action')
        counts['whole_B_empty_requests'] += 1
        if prescribed[0] == 0:
            require(extension[a0] == a0, 'compatible singleton identity with prescribed ENTIRE owner permutation')
            counts['whole_B_singleton_requests'] += 1
    require(counts['whole_B_singleton_requests'] == 2,
            'same singleton request can prescribe TWO different whole-B components')
    # Root transport chooses its component; asking it to satisfy a separate
    # source identity request would be impossible by injectivity of owners.
    root = (1, 1)
    sigma = (1, 0, 2)
    transported = (sigma[root[0]], root[1] ^ 1)
    require(transported == a0, 'root transport can choose an owner-moving component')
    require(not any(g[0] == 0 and g[1] == 0 for g in gamma),
            'do not conflate rooted transport with a separately prescribed source map')
    witnesses['source_vs_root_requests'] = {'source_point_fixed': a0, 'root': root,
                                            'root_image': transported, 'root_owner_component': sigma}
    counts['negative_conflated_source_and_root_requests'] += 1
    tick()


def check():
    global START
    START = time.monotonic()
    signal.signal(signal.SIGALRM, lambda *_: (_ for _ in ()).throw(TimeoutError('30-second diagnostic limit')))
    signal.alarm(30)
    counts, witnesses = Counter(), {}
    for phase in (helper_controls, palette_controls, row_controls, trim_controls, request_controls):
        phase(counts, witnesses)
    signal.alarm(0)
    return {'status': 'PASS', 'scope': 'bounded B028 palette, fixed-row decoder and finite-group diagnostics',
            'counts': dict(sorted(counts.items())), 'witnesses': witnesses,
            'seconds': round(time.monotonic() - START, 3),
            'limits': 'No infinite source, closed-SAP/CCO, HKN, EPPA, ambient lifting or MI theorem certification.'}


if __name__ == '__main__':
    print(json.dumps(check(), sort_keys=True))
