#!/usr/bin/env python3
"""Bounded B033 profile-Helly/fixed-vertex completion diagnostics.

The one-sort subcases enumerate ALL symmetric triangle tables on <=3
diversity colours. Unordered allowed triples give Peircean products; totality,
associativity and finite 2-Helly of positive reachable profiles are checked
independently. Exactly 120 tables pass. No identity colour is added.

Seven representative tables test every partial network on four fixed
vertices against independently enumerated complete legal extensions. The
edge filler recomputes all positive simple path profiles, checks pairwise
intersection (including overlapping/crossed internal orders), chooses one
common colour and preserves algebraic cycle compatibility. Each assignment
decreases the missing-pair count by ONE and changes no old edge or vertex.

All 120 tables also test short possibly NONINJECTIVE homomorphic walks with
distinct actual endpoints and return-square absorption. A four-cycle can
map opposite formal terminals to the SAME actual point: that semantic
collision is tested without reading a fictional diversity edge there.
Independent CSP checks compare profile closure and fixed-cycle completions
for every coloured cycle of lengths 3..5. Free amalgams test empty,
singleton, complete-edge and three-point complete bases. The two-base-point
case is explicitly a contracted digon, not a claimed simple base cycle.

Negative controls drop totality, associativity or 2-Helly separately. The
non-Helly table forbidding monochromatic triangles has a legal K4 clone
type with return profiles 6,5,3: pairwise intersecting, empty total meet.
An artificially size-capped proper subclass and two admitted singleton
sorts with no cross palette separately test the FULL-class/support gates.

Bounds: 1,042 initial triangle tables, <=5 fixed vertices, positive walks
of length <=5; only two legal K4 samples per table in the walk test and
two point-extension types per legal three-point base in the larger SAP
test. Normal timeout 10s, hard SIGALRM/deadline 30s. Reproduce:
  timeout 10s python tools/check_profile_helly_controls.py

These finite algebra/network examples do NOT certify arbitrary typed
palettes, the unbounded path induction, semantic CCO/SAP of a source,
infinite homogeneity, Lean statements, EPPA or coherent extensions.
"""
from collections import Counter
from itertools import combinations, combinations_with_replacement, permutations, product
import json
import signal
import time


START = time.monotonic()
COUNTS = Counter()
WITNESSES = {}


def require(ok, message, witness=None):
    if not ok:
        raise AssertionError((message, witness))
    if time.monotonic() - START > 30:
        raise TimeoutError('30-second B033 diagnostic bound')


def triangle_table(k, bits):
    table = [[0] * k for _ in range(k)]
    for i, triple in enumerate(combinations_with_replacement(range(k), 3)):
        if bits >> i & 1:
            for a, b, c in set(permutations(triple)):
                table[a][b] |= 1 << c
    return table


def multiply(table, left, right):
    out = 0
    for a in range(len(table)):
        if left >> a & 1:
            for b in range(len(table)):
                if right >> b & 1:
                    out |= table[a][b]
    return out


def associative(table):
    return all(multiply(table, table[a][b], 1 << c)
               == multiply(table, 1 << a, table[b][c])
               for a, b, c in product(range(len(table)), repeat=3))


def reachable(table):
    family = {1 << a for a in range(len(table))}
    while True:
        larger = family | {multiply(table, menu, 1 << b)
                           for menu in family for b in range(len(table))}
        if larger == family:
            return family
        family = larger


def two_helly(family):
    for size in range(3, len(family) + 1):
        for subset in combinations(family, size):
            if all(a & b for a, b in combinations(subset, 2)):
                meet = subset[0]
                for item in subset[1:]:
                    meet &= item
                if not meet:
                    return False
    return True


def admissible_tables():
    out = []
    for k in (1, 2, 3):
        for bits in range(1 << (k * (k + 1) * (k + 2) // 6)):
            COUNTS['triangle_tables_enumerated'] += 1
            table = triangle_table(k, bits)
            if any(not entry for row in table for entry in row):
                continue
            if not associative(table) or not two_helly(reachable(table)):
                continue
            out.append((k, bits, table))
    require(len(out) == 120, 'all small total associative Helly tables', len(out))
    return out


def profile(table, word):
    if not word:
        raise ValueError('A reachable profile requires a POSITIVE word')
    out = 1 << word[0]
    for atom in word[1:]:
        out = multiply(table, out, 1 << atom)
    return out


class Network:
    def __init__(self, size):
        self.size = size
        self.edges = tuple(combinations(range(size), 2))
        self.index = {pair: i for i, pair in enumerate(self.edges)}
        self.triples = tuple((self.edge(x, y), self.edge(y, z), self.edge(x, z))
                             for x, y, z in combinations(range(size), 3))
        cycles = set()
        for length in range(3, size + 1):
            for vertices in permutations(range(size), length):
                if vertices[0] != min(vertices) or vertices[1] > vertices[-1]:
                    continue
                cycles.add(tuple(self.edge(vertices[i], vertices[(i + 1) % length])
                                 for i in range(length)))
        self.cycles = tuple(cycles)

    def edge(self, x, y):
        return self.index[tuple(sorted((x, y)))]

    def legal(self, table, labels):
        return all(table[labels[a]][labels[b]] >> labels[c] & 1
                   for a, b, c in self.triples)

    def cycle_compatible(self, table, labels):
        for cycle in self.cycles:
            if all(labels[e] >= 0 for e in cycle):
                word = [labels[e] for e in cycle]
                if not (profile(table, word[:-1]) >> word[-1] & 1):
                    return False
        return True

    def path_profiles(self, table, labels, x, y):
        out = []

        def visit(v, seen, vertices, word):
            if v == y:
                out.append((tuple(vertices), profile(table, word)))
                return
            for z in range(self.size):
                if z not in seen and labels[self.edge(v, z)] >= 0:
                    visit(z, seen | {z}, vertices + [z],
                          word + [labels[self.edge(v, z)]])

        visit(x, {x}, [x], [])
        return out

    def fill(self, table, initial, track_path_orders=False):
        labels = list(initial)
        require(self.cycle_compatible(table, labels), 'initial algebraic cycle invariant')
        missing = labels.count(-1)
        for e, (x, y) in enumerate(self.edges):
            if labels[e] >= 0:
                continue
            paths = self.path_profiles(table, labels, x, y)
            for (p, a), (q, b) in combinations(paths, 2):
                require(a & b, 'pairwise positive path profiles', (initial, p, q, a, b))
                if track_path_orders:
                    common = set(p[1:-1]) & set(q[1:-1])
                    if common:
                        COUNTS['overlapping_simple_path_pairs'] += 1
                    if len(common) >= 2:
                        p_order = [v for v in p if v in common]
                        q_order = [v for v in q if v in common]
                        if p_order != q_order:
                            COUNTS['crossed_common_internal_orders'] += 1
                            WITNESSES.setdefault('crossed_internal_order', [list(p), list(q)])
            allowed = (1 << len(table)) - 1
            for _, menu in paths:
                allowed &= menu
            require(allowed, 'finite Helly common path colour', (initial, x, y, paths))
            labels[e] = (allowed & -allowed).bit_length() - 1
            missing -= 1
            require(labels.count(-1) == missing, 'one missing pair eliminated')
            require(all(old < 0 or old == new for old, new in zip(initial, labels)),
                    'all old edges retained')
            require(self.cycle_compatible(table, labels), 'new-cycle invariant')
            COUNTS['edge_assignments'] += 1
        require(missing == 0 and self.legal(table, labels), 'final fixed-vertex network legal')
        return tuple(labels)


def cycle_csp(table, word):
    """Independent search using only triangles, not profiles/Helly."""
    size = len(word)
    edges = {tuple(sorted((i, (i + 1) % size))): word[i] for i in range(size)}
    pairs = tuple(combinations(range(size), 2))
    full = (1 << len(table)) - 1

    def search():
        missing = []
        for uv in pairs:
            if uv in edges:
                continue
            x, y = uv
            allowed = full
            for z in range(size):
                if z in uv:
                    continue
                a = edges.get(tuple(sorted((x, z))))
                b = edges.get(tuple(sorted((z, y))))
                if a is not None and b is not None:
                    allowed &= table[a][b]
            if not allowed:
                return False
            missing.append((allowed.bit_count(), uv, allowed))
        if not missing:
            return True
        _, uv, allowed = min(missing)
        for atom in range(len(table)):
            if allowed >> atom & 1:
                edges[uv] = atom
                if search():
                    del edges[uv]
                    return True
        del edges[uv]
        return False

    for x, y, z in combinations(range(size), 3):
        a, b, c = edges.get((x, y)), edges.get((y, z)), edges.get((x, z))
        if a is not None and b is not None and c is not None and not (table[a][b] >> c & 1):
            return False
    return search()


def run():
    tables = admissible_tables()
    COUNTS['total_assoc_peirce_helly_tables'] = len(tables)
    four = Network(4)
    for k, bits, table in tables:
        for a, q in product(range(k), repeat=2):
            require(multiply(table, table[a][a], 1 << q) >> q & 1,
                    'positive return-square absorption', (bits, a, q))
            COUNTS['return_square_absorptions'] += 1
        for a, b in product(range(k), repeat=2):
            require(table[a][a] & table[b][b], 'semantic collapsed opposite roots', (bits, a, b))
            COUNTS['collapsed_cycle_terminal_profile_intersections'] += 1
        for length in (3, 4, 5):
            for word in product(range(k), repeat=length):
                algebraic = bool(profile(table, word[:-1]) >> word[-1] & 1)
                require(algebraic == cycle_csp(table, word),
                        'cycle algebra versus independent fixed-network CSP', (bits, word))
                COUNTS['cycle_CSP_comparisons'] += 1

    selected = {(1, 1), (2, 5), (2, 7), (2, 15), (3, 169), (3, 191), (3, 1023)}
    for k, bits, table in tables:
        if (k, bits) not in selected:
            continue
        complete = [v for v in product(range(k), repeat=6) if four.legal(table, v)]
        covers = set()
        for v in complete:
            for mask in range(64):
                covers.add(tuple(v[e] if mask >> e & 1 else -1 for e in range(6)))
        COUNTS['independently_enumerated_complete_K4'] += len(complete)
        for labels in product(range(-1, k), repeat=6):
            algebraic = four.cycle_compatible(table, labels)
            require(algebraic == (labels in covers), 'exact partial network completion', (bits, labels))
            COUNTS['partial_K4_networks'] += 1
            if algebraic:
                four.fill(table, labels, track_path_orders=True)
                COUNTS['fixed_vertex_completions'] += 1

    # Read walks in actual finite complete networks, not an invented edge profile.
    for k, bits, table in tables:
        nets = []
        for labels in product(range(k), repeat=6):
            if four.legal(table, labels):
                nets.append(labels)
            if len(nets) == 2:
                break
        for labels in nets:
            for length in range(1, 6):
                for walk in product(range(4), repeat=length + 1):
                    if walk[0] == walk[-1] or any(x == y for x, y in zip(walk, walk[1:])):
                        continue
                    word = [labels[four.edge(x, y)] for x, y in zip(walk, walk[1:])]
                    require(profile(table, word) >> labels[four.edge(walk[0], walk[-1])] & 1,
                            'distinct-endpoint homomorphic walk readout', (bits, labels, walk))
                    COUNTS['homomorphic_walk_readouts'] += 1
                    if len(set(walk)) < len(walk):
                        COUNTS['noninjective_walks_read_correctly'] += 1

    for k, bits, table in tables:
        for a, b in product(range(k), repeat=2):
            labels = [-1] * 6
            labels[four.edge(0, 1)] = a
            labels[four.edge(2, 3)] = b
            four.fill(table, labels)
            COUNTS['SAP_empty_base_amalgams'] += 1
        for a, b, c, d in product(range(k), repeat=4):
            if not (table[b][d] >> c & 1):
                continue
            labels = [-1] * 6
            for x, y, colour in [(0, 1, a), (0, 2, b), (0, 3, c), (2, 3, d)]:
                labels[four.edge(x, y)] = colour
            four.fill(table, labels)
            COUNTS['SAP_singleton_base_amalgams'] += 1
        for a, b, c, d, e in product(range(k), repeat=5):
            if not (table[a][c] >> b & 1 and table[a][e] >> d & 1):
                continue
            labels = [-1] * 6
            for x, y, colour in [(0, 1, a), (0, 2, b), (1, 2, c), (0, 3, d), (1, 3, e)]:
                labels[four.edge(x, y)] = colour
            four.fill(table, labels)
            COUNTS['SAP_complete_edge_base_digons'] += 1

    five = Network(5)
    for k, bits, table in tables:
        for a, b, c in product(range(k), repeat=3):
            if not (table[a][c] >> b & 1):
                continue
            extensions = []
            for x, y, z in product(range(k), repeat=3):
                if table[a][y] >> x & 1 and table[b][z] >> x & 1 and table[c][z] >> y & 1:
                    extensions.append((x, y, z))
                if len(extensions) == 2:
                    break
            for left, right in product(extensions, repeat=2):
                labels = [-1] * len(five.edges)
                for x, y, colour in [(0, 1, a), (0, 2, b), (1, 2, c)]:
                    labels[five.edge(x, y)] = colour
                for vertex, extension in [(3, left), (4, right)]:
                    for base, colour in enumerate(extension):
                        labels[five.edge(base, vertex)] = colour
                five.fill(table, labels)
                COUNTS['SAP_three_point_complete_base_samples'] += 1

    # Totality is essential to the fixed-vertex conclusion: a single colour
    # with no triangle cannot complete a two-edge fork on three vertices.
    empty = triangle_table(1, 0)
    require(not empty[0][0] and not cycle_csp(empty, (0, 0, 0)), 'non-total palette negative')
    COUNTS['negative_non_total_fork'] += 1
    # Two colours, no monochromatic triangles: total and 2-Helly but NOT associative.
    nonassoc = triangle_table(2, 6)
    require(all(x for row in nonassoc for x in row) and two_helly(reachable(nonassoc))
            and not associative(nonassoc), 'nonassociative negative')
    COUNTS['negative_nonassociative_table'] += 1
    # Three colours, no monochromatic triangles: total associative, NOT 2-Helly.
    nonhelly = triangle_table(3, 446)
    require(associative(nonhelly) and all(x for row in nonhelly for x in row), 'negative table algebra')
    family = [nonhelly[a][a] for a in range(3)]
    require(all(a & b for a, b in combinations(family, 2)) and not (family[0] & family[1] & family[2]),
            'negative return-profile Helly family', family)
    require(four.legal(nonhelly, (0, 1, 2, 2, 1, 0)), 'negative clone base legal')
    COUNTS['negative_pairwise_not_Helly_clone_type'] += 1
    try:
        profile([[1]], ())
    except ValueError:
        COUNTS['negative_empty_profile_word'] += 1
    else:
        raise AssertionError('empty positive word accepted')
    # FULL triangle-defined class is substantive. The same one-colour
    # table admits every K_n, but its artificially capped <=3 subclass
    # omits a triangle-legal K4. Two K3 factors over K2 need four distinct
    # vertices in any STRONG amalgam, so cannot amalgamate in that subclass.
    one_colour = triangle_table(1, 1)
    cap = 3
    factor_size, base_size = 3, 2
    strong_union_size = 2 * factor_size - base_size
    require(Network(3).legal(one_colour, (0, 0, 0)) and factor_size <= cap,
            'proper-subclass factors legal')
    require(four.legal(one_colour, (0,) * 6) and strong_union_size == 4
            and strong_union_size > cap, 'proper subclass is not FULL')
    COUNTS['negative_non_full_triangle_subclass'] += 1
    WITNESSES['non_full_triangle_subclass'] = {
        'table': 'one colour; its sole triangle is allowed',
        'artificial_class_size_cap': cap,
        'factor_sizes': [factor_size, factor_size],
        'complete_base_size': base_size,
        'minimum_strong_amalgam_size': strong_union_size,
        'K4_triangle_legal_but_excluded': True,
        'violated_gate': 'FULL triangle-defined class',
    }
    # Typed support is a separate availability gate. Both singleton sorts
    # are admitted, but their empty-base union needs an unavailable cross
    # pair. This is a countercheck outside the theorem's cross-palette gate,
    # not a claimed failure under its complete typed hypotheses.
    typed_palettes = {('a', 'a'): (0,), ('b', 'b'): (0,),
                      ('a', 'b'): (), ('b', 'a'): ()}

    def supported_vertex_set(sorts):
        return all(typed_palettes[(sorts[x], sorts[y])]
                   for x, y in combinations(range(len(sorts)), 2))

    require(supported_vertex_set(('a',)) and supported_vertex_set(('b',)),
            'both singleton sorts admitted')
    require(not supported_vertex_set(('a', 'b')),
            'empty-base typed union lacks a cross palette')
    COUNTS['negative_unavailable_typed_cross_palette'] += 1
    WITNESSES['unavailable_typed_cross_palette'] = {
        'factor_sorts': [['a'], ['b']],
        'base_vertices': [],
        'required_strong_union_sorts': ['a', 'b'],
        'cross_palette_a_b': [],
        'violated_gate': 'nonempty palette for every required cross pair',
    }
    WITNESSES.update(collapsed_formal_cycle={'map': [0, 1, 0, 2],
                                           'opposite_formal_terminals_equal': True,
                                           'specified_edge_images_distinct': True},
                     non_Helly_return_profiles=family,
                     non_Helly_legal_K4=[0, 1, 2, 2, 1, 0],
                     base_edge_case='two shared base points contract to a digon, not a simple cycle',
                     no_vertex_identifications='all fills retain original vertex set and all old edges')
    require(COUNTS['crossed_common_internal_orders'] > 0, 'crossed-order path case reached')
    return {'status': 'PASS', 'scope': 'bounded profile algebra, hom-walk and fixed-vertex completion checks',
            'counts': dict(COUNTS), 'witnesses': WITNESSES,
            'seconds': round(time.monotonic() - START, 3),
            'limits': 'Finite one-sort examples do not certify arbitrary typed palettes, unbounded path induction, source CCO/SAP, homogeneity, Lean or EPPA.'}


if __name__ == '__main__':
    def expired(_signum, _frame):
        raise TimeoutError('30-second B033 hard deadline')
    signal.signal(signal.SIGALRM, expired)
    signal.alarm(30)
    print(json.dumps(run(), sort_keys=True))
