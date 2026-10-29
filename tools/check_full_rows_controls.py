#!/usr/bin/env python3
"""Independent, bounded diagnostics for the R07 full-row formulas.

Integers with XOR implement F2 and F2^2.  Legal correction matrices are
exhaustively enumerated, independently of RC1/RC2; requests are compared
with their literal actions on full rows.  The relation-triangle controls
are finite binary CSPs with relational composition, not claimed actual
infinite CCO sources, exact-menu providers, or a certification of the
manuscript's completion/reading hypotheses.  No other control is imported.
"""
from collections import Counter
from itertools import combinations, permutations, product
from random import Random


def require(condition, message):
    if not condition:
        raise AssertionError(message)


def graphs(n):
    pairs = tuple(combinations(range(n), 2))
    for flags in product((False, True), repeat=len(pairs)):
        yield frozenset(p for p, yes in zip(pairs, flags) if yes)


def legal_matrices(n, order, records):
    """Brute force the entire matrix cube; do not construct via RC1/RC2."""
    return tuple(c for c in product(range(order), repeat=n * n)
                 if all(c[i * n + j] == c[j * n + i]
                        for i, j in combinations(range(n), 2)
                        if (i, j) not in records))


def image_row(i, f, sigma, b, c):
    n = len(sigma)
    target = [None] * n
    for j in range(n):
        target[sigma[j]] = f[j] ^ c[i * n + j] ^ b[i]
    return tuple(target)


def criterion(request, sigma, b, records):
    """The two stated finite conditions, separate from the action oracle."""
    forced = {}
    for i, f, target in request:
        row = tuple(target[sigma[j]] ^ f[j] ^ b[i] for j in range(len(sigma)))
        if i in forced and forced[i] != row:
            return False
        forced[i] = row
    return all(forced[i][j] == forced[j][i]
               for i, j in combinations(forced, 2)
               if tuple(sorted((i, j))) not in records)


def action_oracle(n, rows, sigma, b, matrices):
    # Each bit is one independently enumerated legal matrix.  Index literal
    # row images, then intersect these sets for simultaneous requests.
    images = {}
    for bit, c in enumerate(matrices):
        flag = 1 << bit
        for i in range(n):
            for f in rows:
                key = (i, f, image_row(i, f, sigma, b, c))
                images[key] = images.get(key, 0) | flag
    return images, (1 << len(matrices)) - 1


def check_request(request, sigma, b, records, oracle, all_matrices, counts):
    available = all_matrices
    for item in request:
        available &= oracle.get(item, 0)
    expected = criterion(request, sigma, b, records)
    require(bool(available) == expected, 'RC1/RC2 iff literal simultaneous legal-matrix action')
    counts['compatible_requests' if expected else 'incompatible_requests'] += 1
    counts['row_requests'] += 1
    return available


def compatibility(counts):
    for n in range(1, 4):
        rows = tuple(product(range(2), repeat=n))
        for records in graphs(n):
            matrices = legal_matrices(n, 2, records)
            counts['compatibility_graphs'] += 1
            counts['exhaustive_legal_matrices'] += len(matrices)
            # Untouched diagonals really are independent: toggling any
            # diagonal of any legal matrix remains in the enumerated set.
            matrix_set = set(matrices)
            for c in matrices:
                for i in range(n):
                    changed = list(c)
                    changed[i * n + i] ^= 1
                    require(tuple(changed) in matrix_set, 'diagonal is unconstrained')
                    counts['free_diagonal_checks'] += 1
            for sigma in permutations(range(n)):
                for b in product(range(2), repeat=n):
                    oracle, all_matrices = action_oracle(n, rows, sigma, b, matrices)
                    # Exhaust every possible forced row at every touched
                    # index, including all touched subsets and empty request.
                    for choices in product((None,) + rows, repeat=n):
                        request = []
                        for i, forced in enumerate(choices):
                            if forced is not None:
                                f = rows[(i + sum(forced)) % len(rows)]
                                target = [0] * n
                                for j in range(n):
                                    target[sigma[j]] = f[j] ^ forced[j] ^ b[i]
                                request.append((i, f, tuple(target)))
                        check_request(request, sigma, b, records, oracle, all_matrices, counts)
                    if n == 2:
                        packets = tuple(product(range(n), rows))
                        # Exhaust all actual source sets of size <=2 and
                        # every target row, including two rows at one index.
                        for size in (0, 1, 2):
                            for selected in combinations(packets, size):
                                for targets in product(rows, repeat=size):
                                    request = tuple((i, f, r) for (i, f), r in zip(selected, targets))
                                    available = check_request(request, sigma, b, records,
                                                              oracle, all_matrices, counts)
                                    if size == 2 and selected[0][0] == selected[1][0]:
                                        counts['same_index_two_row_requests'] += 1
                                        if targets == ((0, 0), (0, 0)):
                                            require(not available, 'distinct same-index rows cannot both zero')
                                            counts['negative_same_index_zeroing'] += 1
                    # One arbitrary actual row per index of EVERY recorded
                    # clique can be zeroed; also include zero-row sources.
                    for size in range(n + 1):
                        for touched in combinations(range(n), size):
                            if any((i, j) not in records for i, j in combinations(touched, 2)):
                                continue
                            for selected in product(rows, repeat=size):
                                request = tuple((i, f, (0,) * n) for i, f in zip(touched, selected))
                                require(check_request(request, sigma, b, records, oracle,
                                                      all_matrices, counts), 'recorded-clique zeroing exists')
                                counts['recorded_clique_zeroings'] += 1
                                if all(f == (0,) * n for f in selected):
                                    counts['zero_row_source_requests'] += 1
    # The second sharp negative obstruction: independently forced values
    # at opposite ends of an unrecorded edge need not agree.
    n, rows, sigma, b = 2, tuple(product(range(2), repeat=2)), (0, 1), (0, 0)
    oracle, all_matrices = action_oracle(n, rows, sigma, b, legal_matrices(n, 2, frozenset()))
    request = ((0, (0, 1), (0, 0)), (1, (0, 0), (0, 0)))
    require(not check_request(request, sigma, b, frozenset(), oracle, all_matrices, counts),
            'independent opposite forced entries violate unrecorded symmetry')
    counts['negative_independent_unrecorded_rows'] += 1


def lift_checks(n, order, records, sigma, b, c, counts):
    rows = tuple(product(range(order), repeat=n))
    vertices = tuple((i, f, z) for i, f, z in product(range(n), rows, range(order)))
    mapping = {(i, f, z): (sigma[i], image_row(i, f, sigma, b, c), z ^ b[i])
               for i, f, z in vertices}
    require(len(set(mapping.values())) == len(vertices), 'literal full-row lift is bijective')
    require(len(vertices) == n * order ** (n + 1), 'exact full-row universe size')
    counts['lift_bijections'] += 1
    for x, ax in mapping.items():
        i, f, z = x
        require((ax[0], ax[2]) == (sigma[i], z ^ b[i]), 'q alpha = s q')
        for g in range(order):
            require(mapping[(i, f, z ^ g)] == (ax[0], ax[1], ax[2] ^ g), 'lift commutes with thin translations')
            counts['thin_commutation_checks'] += 1
        for j in range(n):
            require(ax[2] ^ ax[1][sigma[j]] == z ^ f[j] ^ c[i * n + j],
                    'effective row covariance at every coordinate')
            counts['effective_row_entries'] += 1
        counts['projection_intertwinings'] += 1
    # A literal finite recorded diagram with fine colours c_ij+z+w.
    # Transport the structural records by s, rather than silently assuming
    # arbitrary sigma,b preserve a separately chosen fixed diagram.
    source_colours = {(i, j): (i ^ j) % order for i, j in records}
    target_colours = {tuple(sorted((sigma[i], sigma[j]))): colour ^ b[i] ^ b[j]
                      for (i, j), colour in source_colours.items()}
    target_records = frozenset(target_colours)
    is_automorphism = target_records == records and target_colours == source_colours
    if is_automorphism:
        counts['fixed_record_diagram_automorphism_lifts'] += 1
    for x, y in combinations(vertices, 2):
        i, f, z = x
        j, k, w = y
        ax, ay = mapping[x], mapping[y]
        if (i, f) == (j, k):
            require(ax[:2] == ay[:2] and ax[2] ^ ay[2] == z ^ w, 'same-packet thin colour')
            counts['same_packet_thin_pairs'] += 1
            continue
        require(ax[:2] != ay[:2], 'distinct actual packets remain distinct')
        recorded = tuple(sorted((i, j))) in records if i != j else False
        image_recorded = tuple(sorted((ax[0], ay[0]))) in target_records if ax[0] != ay[0] else False
        require(recorded == image_recorded, 'record/hole status transported, including same index')
        u = z ^ f[j] ^ w ^ k[i]
        image_u = ax[2] ^ ax[1][ay[0]] ^ ay[2] ^ ay[1][ax[0]]
        require(image_u == u ^ c[i * n + j] ^ c[j * n + i], 'effective reading-parameter formula')
        if not recorded:
            require(image_u == u, 'reading parameter invariant on every actual hole')
            counts['unrecorded_parameter_pairs'] += 1
            if i == j:
                counts['same_index_unrecorded_pairs'] += 1
        else:
            key, image_key = tuple(sorted((i, j))), tuple(sorted((ax[0], ay[0])))
            require(source_colours[key] ^ z ^ w == target_colours[image_key] ^ ax[2] ^ ay[2],
                    'all recorded fine-matrix entries preserved under structural transport')
            counts['recorded_fine_pairs'] += 1


def lifts(counts):
    for n, order in ((1, 2), (2, 2), (3, 2), (2, 4)):
        for records in graphs(n):
            matrices = legal_matrices(n, order, records)
            # Exhaust |I|<=2 over F2; bound the larger diagnostic suites.
            if n == 3 or order == 4:
                matrices = tuple(dict.fromkeys(matrices[k] for k in
                                 (0, len(matrices) // 3, 2 * len(matrices) // 3, len(matrices) - 1)))
            for sigma in permutations(range(n)):
                if n == 3 and sigma not in (tuple(range(n)), tuple(reversed(range(n)))):
                    continue
                shifts = tuple(product(range(order), repeat=n))
                if n == 3:
                    shifts = (shifts[0], shifts[-1])
                if order == 4:
                    shifts = ((0, 0), (1, 2), (2, 2), (3, 1))
                for b, c in product(shifts, matrices):
                    lift_checks(n, order, records, sigma, b, c, counts)
    # The diagonal is the actual t_g, with the entire valuation row fixed.
    # Owners are F2 and G=F2^2 acts through its low bit, so 2 is a nontrivial
    # owner stabiliser.  Real packet translations are still free.
    for n in (1, 2, 3):
        order = 4
        beta = tuple(i % 2 for i in range(n))
        for g in range(order):
            sigma, b, c = tuple(range(n)), (g,) * n, (g,) * (n * n)
            for records in graphs(n):
                require(all(c[i * n + j] ^ c[j * n + i] == 0
                            for i, j in combinations(range(n), 2) if (i, j) not in records),
                        'constant diagonal matrix legal')
                counts['constant_diagonal_graphs'] += 1
            for i, f, z in product(range(n), product(range(order), repeat=n), range(order)):
                target = (sigma[i], image_row(i, f, sigma, b, c), z ^ b[i])
                require(target == (i, f, z ^ g), 'constant C=g,b=g gives actual t_g and unchanged full row')
                owner_before, owner_after = (z & 1) ^ beta[i], (target[2] & 1) ^ beta[target[0]]
                require(owner_after == owner_before ^ (g & 1), 'nonfaithful actual owner action')
                if g == 2:
                    require(target != (i, f, z) and owner_after == owner_before,
                            'stabiliser translation nontrivial on real packet, trivial on owner')
                    counts['nonfaithful_owner_stabiliser_vertices'] += 1
                counts['constant_diagonal_vertices'] += 1


class Relations:
    """All binary relations on a finite set; atoms are literal ordered pairs."""
    def __init__(self, size):
        self.size = size
        self.full = (1 << (size * size)) - 1
        self._composition = {}
        self._converse = {}

    def atom(self, a, b):
        return 1 << (a * self.size + b)

    def converse(self, mask):
        if mask not in self._converse:
            self._converse[mask] = sum(self.atom(b, a)
                                      for a, b in product(range(self.size), repeat=2)
                                      if mask & self.atom(a, b))
        return self._converse[mask]

    def compose(self, left, right):
        key = (left, right)
        if key not in self._composition:
            result = 0
            for a, b, c in product(range(self.size), repeat=3):
                if left & self.atom(a, b) and right & self.atom(b, c):
                    result |= self.atom(a, c)
            self._composition[key] = result
        return self._composition[key]

    def switch(self, mask, left, right):
        return sum(self.atom(a ^ left, b ^ right)
                   for a, b in product(range(self.size), repeat=2) if mask & self.atom(a, b))


def family(n, upper, algebra):
    domains = {}
    for (i, j), mask in zip(combinations(range(n), 2), upper):
        domains[i, j], domains[j, i] = mask, algebra.converse(mask)
    return domains


def pc(initial, n, algebra, schedule, counts=None):
    domains = dict(initial)
    while True:
        changed = False
        for p, q, r in schedule:
            new = domains[p, q] & algebra.compose(domains[p, r], domains[r, q])
            if new != domains[p, q]:
                domains[p, q], domains[q, p] = new, algebra.converse(new)
                changed = True
                if counts is not None:
                    counts['pc_strict_contractions'] += 1
        if not changed:
            return domains


def solutions(domains, n, algebra):
    return tuple(values for values in product(range(algebra.size), repeat=n)
                 if all(domains[i, j] & algebra.atom(values[i], values[j])
                        for i, j in combinations(range(n), 2)))


def subsets(mask):
    result = [0]
    bit = 1
    while bit <= mask:
        if mask & bit:
            result += [m | bit for m in result]
        bit <<= 1
    return result


def pc_controls(counts):
    algebra, n = Relations(2), 3
    triples = tuple(permutations(range(n), 3))
    shuffled = list(triples)
    Random(7103).shuffle(shuffled)
    schedules = (triples, tuple(reversed(triples)), tuple(shuffled))
    # Every initial edge includes the planted solution (0,0), with every
    # combination of the other three relation atoms exhaustively covered.
    menus = tuple(mask for mask in range(16) if mask & algebra.atom(0, 0))
    for upper in product(menus, repeat=3):
        initial = family(n, upper, algebra)
        terminal = pc(initial, n, algebra, schedules[0], counts)
        for schedule in schedules[1:]:
            require(pc(initial, n, algebra, schedule) == terminal, 'fair PC schedules have identical limits')
            counts['pc_schedule_comparisons'] += 1
        require(all(terminal.values()), 'planted solution keeps every menu nonempty')
        original_solutions = solutions(initial, n, algebra)
        for values in original_solutions:
            require(all(terminal[i, j] & algebra.atom(values[i], values[j])
                        for i, j in combinations(range(n), 2)), 'every actual solution survives every edge')
            counts['pc_surviving_solutions'] += 1
        for edge, mask in initial.items():
            if mask.bit_count() == 1:
                require(terminal[edge] == mask, 'prescribed singleton record survives')
                counts['pc_singleton_records'] += 1
        require(pc(terminal, n, algebra, schedules[0]) == terminal, 'terminal is common PC fixed family')
        # Exhaust ALL subfamilies, including empty menus, below this initial
        # family: greatest-fixed-point assertion independent of schedules.
        for candidate_upper in product(*(subsets(mask) for mask in upper)):
            candidate = family(n, candidate_upper, algebra)
            fixed = all(candidate[p, q] & ~algebra.compose(candidate[p, r], candidate[r, q]) == 0
                        for p, q, r in triples)
            if fixed:
                require(all(candidate[edge] & ~terminal[edge] == 0 for edge in candidate),
                        'every common fixed subfamily is below computed terminal')
                counts['pc_fixed_subfamilies'] += 1
            counts['pc_subfamilies_enumerated'] += 1
        for delta in product(range(2), repeat=n):
            moved = {edge: algebra.switch(mask, delta[edge[0]], delta[edge[1]])
                     for edge, mask in initial.items()}
            moved_terminal = pc(moved, n, algebra, schedules[0])
            require(moved_terminal == {edge: algebra.switch(mask, delta[edge[0]], delta[edge[1]])
                                      for edge, mask in terminal.items()}, 'endpoint gauge naturality of greatest PC family')
            counts['pc_endpoint_gauges'] += 1
        counts['pc_exhaustive_initial_networks'] += 1
    # Check the represented product law itself, for arbitrary (also empty)
    # relations, with independent endpoint shifts and middle cancellation.
    for left, right, dp, dr, dq in product(range(16), range(16), range(2), range(2), range(2)):
        require(algebra.compose(algebra.switch(left, dp, dr), algebra.switch(right, dr, dq))
                == algebra.switch(algebra.compose(left, right), dp, dq), 'represented gauge-product law')
        counts['pc_gauge_product_checks'] += 1
    # Larger finite relation networks with F2^2 endpoint gauges and several
    # independently planted solutions, using all sixteen ordered-pair atoms.
    algebra, n, rng = Relations(4), 4, Random(7104)
    triples = tuple(permutations(range(n), 3))
    for case in range(32):
        planted = tuple(tuple(rng.randrange(4) for _ in range(n)) for _ in range(2))
        upper = []
        for i, j in combinations(range(n), 2):
            mask = 0
            for values in planted:
                mask |= algebra.atom(values[i], values[j])
            for a, b in product(range(4), repeat=2):
                if rng.randrange(4) == 0:
                    mask |= algebra.atom(a, b)
            upper.append(mask)
        initial = family(n, upper, algebra)
        terminal = pc(initial, n, algebra, triples, counts)
        shuffled = list(triples)
        rng.shuffle(shuffled)
        require(pc(initial, n, algebra, tuple(shuffled)) == terminal, 'larger relation-network fair schedule')
        counts['pc_schedule_comparisons'] += 1
        for values in solutions(initial, n, algebra):
            require(all(terminal[i, j] & algebra.atom(values[i], values[j])
                        for i, j in combinations(range(n), 2)), 'all larger-network solutions survive')
            counts['pc_surviving_solutions'] += 1
        delta = tuple(rng.randrange(4) for _ in range(n))
        moved = {edge: algebra.switch(mask, delta[edge[0]], delta[edge[1]])
                 for edge, mask in initial.items()}
        require(pc(moved, n, algebra, triples) ==
                {edge: algebra.switch(mask, delta[edge[0]], delta[edge[1]])
                 for edge, mask in terminal.items()}, 'F2^2 endpoint gauge naturality')
        counts['pc_endpoint_gauges'] += 1
        counts['pc_larger_initial_networks'] += 1
    # A finite CSP limit diagnostic: K4 cannot be coloured with three values,
    # but every inequality edge is path-consistent.  This is deliberately
    # not an actual infinite CCO counterexample or an exact-menu claim.
    algebra, n = Relations(3), 4
    inequality = sum(algebra.atom(a, b) for a, b in product(range(3), repeat=2) if a != b)
    initial = family(n, (inequality,) * 6, algebra)
    terminal = pc(initial, n, algebra, tuple(permutations(range(n), 3)))
    require(terminal == initial and not solutions(initial, n, algebra),
            'PC can leave nonempty menus without any global CSP solution')
    counts['pc_nonempty_without_global_solution_diagnostic'] += 1


def main():
    counts = Counter()
    compatibility(counts)
    lifts(counts)
    pc_controls(counts)
    require(counts['same_index_two_row_requests'] and counts['same_index_unrecorded_pairs']
            and counts['nonfaithful_owner_stabiliser_vertices'] and counts['pc_strict_contractions'],
            'diagnostics exercise the required nonvacuous cases')
    print('Full-row finite controls passed (stdlib; exhaustive F2 compatibility, |I|=1..3).')
    for key, value in sorted(counts.items()):
        print(f'  {key}: {value}')
    print('Limits: larger lift suites are bounded samples; arbitrary structural maps transport recorded diagrams, '
          'and the reported fixed-diagram subset gives actual finite record automorphisms. '
          'PC uses literal finite relation triangles, with exhaustive greatest-fixed-point checks on 512 '
          'three-variable binary networks and 32 larger planted-solution networks. '
          'No assertion that PC equals global completion spectra; no CCO, actual exact-menu, '
          'reading, reservoir-completion, or unrestricted EPPA certification.')


if __name__ == '__main__':
    main()
