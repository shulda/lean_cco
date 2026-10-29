#!/usr/bin/env python3
"""Bounded B026 safe-trace/moving-reading diagnostics; no theorem certification.

Representation: four diversity atoms R,B,N0,N1; forbid precisely monochromatic
R and B triangles. Named owners are bits s,t; their literal fine palette is
{(s XOR t,c):c in 0..3}. Logical equality is NOT an atom. Triangle vertices
are distinct formal vertices even when owner labels repeat. The safe set
{R,N0} contains a universally legal neutral colour. Exact menus are computed
from finite positive-word profiles and nonempty intersections, not declared
all subsets. Safe traces add a genuinely nonexact menu.

Endpoint C2 switching toggles the literal palette bit and exchanges N0,N1.
Pure Gamma=C2 x C2 flips BOTH owners with the first coordinate, fixes literal
colours, and has a nonfaithful second-coordinate kernel. These are finite
triangle-table/action diagnostics; no actual finite-kernel realization,
infinite source, SAP, CCO, primitivity, HKN reservoir or EPPA is certified.

Search preflight: colour names/owner actions fixed, no label enumeration.
At most 4,164 labelled complete diagrams through four vertices (4^6+4^3+4),
32,768 rectangular tests, 15^3 subset associativity tests, and <2.5 million
normal-form steps. Products are cached 4-bit masks. Complexity is constant
for this fixed scope, dominated by O(4^6 * 6 * 4) diagram triangle checks.
Pilot: `timeout 10s python tools/check_safe_readings_controls.py`.
Full limit: 30 seconds via SIGALRM, with explicit phase deadline checks.
No unbounded closure: each closure is bounded by all 16 possible masks.
On success print one JSON checkpoint; redirect stdout to a chosen scratch
checkpoint path. On failure an assertion includes the finite witness.
Reproduce from the manuscript root; no other control script is imported.
"""
from collections import Counter
from itertools import combinations, product
import json
import signal
import time

TOP, SAFE = 15, 5  # {R,B,N0,N1}; {R,N0}
ATOMS = tuple(range(4))
NONEMPTY = tuple(range(1, 16))
START = time.monotonic()


def require(ok, message, witness=None):
    if not ok:
        raise AssertionError((message, witness))


def tick():
    require(time.monotonic() - START < 30, '30-second diagnostic deadline')


def legal(a, b, c):
    return not (a == b == c and a in (0, 1))


def atoms(mask):
    return tuple(a for a in ATOMS if mask & (1 << a))


def build_products():
    atomic = {(a, b): sum(1 << c for c in ATOMS if legal(a, b, c))
              for a, b in product(ATOMS, repeat=2)}
    # Literal triangle witnesses define the independent atomic-product oracle.
    return {(a, b): sum(1 << c for c in ATOMS
                           if any(atomic[x, y] & (1 << c)
                                  for x in atoms(a) for y in atoms(b)))
            for a, b in product(range(16), repeat=2)}


MUL = build_products()


def mul(a, b):
    return MUL[a, b]


def pc(a, b, c):
    return not ((c & ~mul(a, b)) or (a & ~mul(c, b)) or (b & ~mul(a, c)))


def exact_menus():
    profiles = {1 << a for a in ATOMS}
    for _ in range(16):
        enlarged = profiles | {mul(a, b) for a, b in product(profiles, repeat=2)}
        if profiles == enlarged:
            break
        profiles = enlarged
    else:
        raise AssertionError('profile closure exceeded the complete mask universe')
    exact = profiles | {TOP}
    for _ in range(16):
        enlarged = exact | {a & b for a, b in product(exact, repeat=2) if a & b}
        if exact == enlarged:
            return tuple(sorted(exact))
        exact = enlarged
    raise AssertionError('exact closure exceeded the complete mask universe')


EXACT = exact_menus()
AUGMENTED = tuple(sorted(set(EXACT) | {x & SAFE for x in EXACT if x & SAFE}))


def retract(x):
    return x & SAFE or x


def choose_kind(x):
    require(x in AUGMENTED, 'selector domain', x)
    if x.bit_count() == 1:
        return atoms(x)[0]
    require(x & 4, 'all nonsingleton menus have N0', x)
    return 2


def swap_kind(c, g):
    return c ^ g if c >= 2 else c


def palette(s, t):
    return frozenset(4 * (s ^ t) + c for c in ATOMS)


def menu(s, t, mask):
    return frozenset(4 * (s ^ t) + c for c in atoms(mask))


def translate_colour(c, g):
    return 4 * ((c // 4) ^ g) + swap_kind(c % 4, g)


def translate_menu(d, g):
    return frozenset(translate_colour(c, g) for c in d)


def choose(s, t, d):
    require(bool(d) and d <= palette(s, t), 'literal owner-palette typing', (s, t, d))
    mask = sum(1 << (c % 4) for c in d)
    return 4 * (s ^ t) + choose_kind(mask)


def reading(s, t, d, g):
    return translate_colour(choose(s ^ g, t, translate_menu(d, g)), g)


def algebra_controls(counts):
    require(EXACT == (1, 2, 4, 8, 12, 13, 14, 15), 'nontrivial exact family', EXACT)
    require(SAFE not in EXACT and SAFE in AUGMENTED, 'genuinely NONEXACT safe trace')
    require(mul(1, 1) == 14 and mul(2, 2) == 13,
            'triangle constraints are nontrivial, not an all-free table')
    for a, b, c in product(NONEMPTY, repeat=3):
        require(mul(mul(a, b), c) == mul(a, mul(b, c)),
                'arbitrary-subset associativity', (a, b, c))
        counts['subset_associativity'] += 1
    for w in NONEMPTY:
        require(mul(w, TOP) == mul(TOP, w) == TOP, 'arbitrary-subset absorption', w)
        power = w
        for n in range(2, 11):
            power = mul(power, w)
            if n >= 8:
                require(power == TOP, 'uniform 2|P| loop bound and later powers', (w, n))
                counts['uniform_loop_powers'] += 1
        counts['nonexact_loop_subsets'] += int(w not in EXACT)
    # An imprimitive infinite two-block orbital table: 0 means within-block
    # DIVERSITY, not logical equality. Its cross-block powers alternate.
    parity_mul = lambda a, b: sum(1 << c for c in range(2)
                                if any((x ^ y) == c for x in range(2) for y in range(2)
                                       if a & (1 << x) and b & (1 << y)))
    parity_power = 2
    for _ in range(3):
        parity_power = parity_mul(parity_power, 2)
    require(parity_power == 1 != 3, 'primitivity is necessary, not stabilization alone')
    counts['negative_imprimitive_uniform_power'] += 1
    tick()


def augmented_controls(counts):
    presentations = tuple((d, flag, d & SAFE if flag else d)
                          for d in EXACT for flag in (0, 1)
                          if (d & SAFE if flag else d))
    for (d, _, x), (e, _, y) in product(presentations, repeat=2):
        require(mul(x, y) == mul(d, e) in EXACT,
                'AS1 for EVERY chosen skeleton presentation', (d, e, x, y))
        counts['all_skeleton_products'] += 1
    for x, y, z in product(AUGMENTED, repeat=3):
        if y & z:
            require(y & z in AUGMENTED, 'nonempty meet closure', (y, z))
            require(mul(x, y & z) == (mul(x, y) & mul(x, z)),
                    'AS3 only at nonempty meets', (x, y, z))
            counts['nonempty_distribution'] += 1
        if pc(x, y, z):
            rx, ry, rz = retract(x), retract(y), retract(z)
            require(pc(rx, ry, rz), 'safe pre-gate preserves ALL three PC coordinates', (x, y, z))
            require(legal(choose_kind(x), choose_kind(y), choose_kind(z)),
                    'joint singleton selector preserves actual triangle legality', (x, y, z))
            counts['nontrivial_PC_selector_triples'] += 1
    for x, y in product(AUGMENTED, repeat=2):
        require(retract(x) in AUGMENTED and retract(retract(x)) == retract(x),
                'safe retraction and image')
        if not (y & ~x) and y & retract(x):
            require(retract(y) == (y & retract(x)), 'safe pre-gate survivor heredity', (x, y))
        if not (y & ~x) and y & (1 << choose_kind(x)):
            require(choose_kind(y) == choose_kind(x), 'individual singleton survivor heredity', (x, y))
        for e in NONEMPTY:
            require(mul(retract(x), e) == mul(x, e),
                    'safe trace identity with arbitrary, possibly nonexact multiplier', (x, e))
            counts['arbitrary_multiplier_identities'] += 1
    for size in range(len(AUGMENTED) + 1):
        for family in combinations(AUGMENTED, size):
            if all(a & b for a, b in combinations(family, 2)):
                meet = TOP
                for x in family:
                    meet &= x
                require(bool(meet), 'augmented finite Helly, including empty list', family)
                counts['pairwise_intersecting_augmented_families'] += 1
    # Empty intersections cannot be fed into nonempty-result distributivity.
    require(mul(TOP, 1 & 2) == 0 and (mul(TOP, 1) & mul(TOP, 2)) == TOP,
            'negative empty-meet distributivity witness')
    # A singleton outside S stays unchanged; it must not become an empty menu.
    require(retract(2) == 2 and retract(8) == 8, 'unsafe singleton exception')
    counts['negative_empty_distribution'] += 1
    tick()


def recolouring_controls(counts):
    for n in (2, 3, 4):
        pairs = tuple(combinations(range(n), 2))
        triangles = tuple(combinations(range(n), 3))
        for values in product(ATOMS, repeat=len(pairs)):
            graph = dict(zip(pairs, values))
            counts['complete_diagrams_examined'] += 1
            if not all(legal(graph[i, j], graph[j, k], graph[i, k])
                       for i, j, k in triangles):
                continue
            for edge in pairs:
                changed = dict(graph)
                changed[edge] = 2  # A literal allowed safe cross edge.
                require(all(legal(changed[i, j], changed[j, k], changed[i, k])
                            for i, j, k in triangles),
                        'same-set one-edge recolouring retains actual triangle legality', (n, graph, edge))
                require(all(changed[e] == graph[e] for e in pairs if e != edge),
                        'every other specified edge is retained', (n, graph, edge))
                counts['safe_single_edge_recolourings'] += 1
    tick()


def reading_controls(counts):
    for s, t in product(range(2), repeat=2):
        for d in EXACT:
            actual = menu(s, t, d)
            for g in range(2):
                a = reading(s, t, actual, g)
                require(a in actual, 'reading conservative in ORIGINAL palette', (s, t, d, g))
                require(a == reading(t, s, actual, g), 'typed converse compatibility', (s, t, d, g))
                for v in range(2):
                    require(reading(s ^ v, t, translate_menu(actual, v), g ^ v)
                            == translate_colour(a, v), 'actual switching identity', (s, t, d, g, v))
                    counts['switching_identities'] += 1
                for owner_action, kernel in product(range(2), repeat=2):
                    require(reading(s ^ owner_action, t ^ owner_action, actual, g) == a,
                            'pure Gamma covariance, including nonfaithful kernel',
                            (s, t, d, g, owner_action, kernel))
                    counts['nonfaithful_Gamma_covariance'] += 1
                for e in EXACT:
                    smaller = menu(s, t, e)
                    if smaller <= actual and a in smaller:
                        require(reading(s, t, smaller, g) == a,
                                'each independently shifted reading is survivor hereditary', (s, t, d, e, g))
                counts['typed_readings'] += 1
            # A forbidden UNMOVED owner pair is genuinely ill-typed here.
            require(not translate_menu(actual, 1) <= palette(s, t),
                    'unshifted h_st(gD) is ill-typed for this actual palette', (s, t, d))
            counts['negative_unmoved_endpoint_typing'] += 1
    for s, t, u in product(range(2), repeat=3):
        for d, a, p in product(EXACT, repeat=3):
            if d & ~mul(p, a) or a & ~mul(d, p):
                continue
            for g, k in product(range(2), repeat=2):
                da = reading(s, t, menu(s, t, d), g) % 4
                aa = reading(t, u, menu(t, u, a), k) % 4
                require(bool(p & mul(1 << da, 1 << aa)),
                        'bilateral support for independently selected pair', (s, t, u, d, a, p, g, k))
                counts['bilateral_support_tests'] += 1
            if not pc(d, a, p):
                continue
            for g, k, ell in product(range(2), repeat=3):
                chosen = (reading(s, t, menu(s, t, d), g),
                          reading(t, u, menu(t, u, a), k),
                          reading(s, u, menu(s, u, p), ell))
                require(all(c in palette(x, y) for c, x, y in
                            zip(chosen, (s, t, s), (t, u, u))), 'three output palette typings', chosen)
                require(legal(*(c % 4 for c in chosen)),
                        'literal rectangular triangle for THREE independent shifts',
                        (s, t, u, d, a, p, g, k, ell, chosen))
                counts['rectangular_independent_shift_triples'] += 1
                counts['no_g_plus_k_equals_ell_assumption'] += int(g ^ k != ell)
                counts['repeated_owner_triangle_tests'] += int(s == t or t == u or s == u)
    require(reading(0, 0, menu(0, 0, TOP), 0)
            != reading(0, 0, menu(0, 0, TOP), 1), 'readings are nonconstant in their shift')
    require(translate_menu(menu(0, 0, SAFE), 1) != menu(1, 0, SAFE),
            'pure-owner safe palette is not unilaterally thin-invariant')
    counts['negative_unilateral_safety_invariance'] += 1
    tick()


def return_controls(counts):
    # None is an ABSENT operation, never a strong identity atom. Finite normal
    # forms retain a positive-factor flag separately from their set value.
    bound = 4 * 4 * 4  # 4 |Gamma| max_t |P_tt|; Gamma has order four.
    for s, t, gamma, converse in product(range(2), repeat=4):
        first, last = (t ^ gamma, s ^ gamma) if converse else (s ^ gamma, t ^ gamma)
        for left, right in product((None,) + EXACT, repeat=2):
            if left is None and first != s or right is None and last != t:
                continue  # An absent factor cannot repair a mismatched sort.
            if left is None and right is None:
                continue
            for d in NONEMPTY:
                value = d
                for _ in range(bound):
                    if left is not None:
                        value = mul(left, value)
                    if right is not None:
                        value = mul(value, right)
                require(value == TOP, 'uniform positive return saturation',
                        (s, t, gamma, converse, left, right, d))
                counts['positive_return_normal_forms'] += 1
    require(not any(all(mul(1 << a, x) == x and mul(x, 1 << a) == x
                        for x in NONEMPTY) for a in ATOMS),
            'NO diversity atom substitutes for an absent identity operation')
    # Directed counterexample: converse exchanges literal a,b; pure owner
    # relabeling fixes them. Parallel singleton a reaches b without multiplying.
    first = (0, 1, 'a')
    converse = (first[1], first[0], 'b')
    pure_owner_swap = (1 - converse[0], 1 - converse[1], converse[2])
    require(pure_owner_swap[:2] == first[:2] and pure_owner_swap[2] != first[2],
            'parallel separation fails for nonsymmetric original literal names')
    require(not any(choice == 1 - choice for choice in range(2)),
            'directed converse/pure-owner covariance has no singleton selector')
    counts['negative_directed_converse_scope'] += 1
    tick()


def check():
    global START
    START = time.monotonic()
    signal.signal(signal.SIGALRM, lambda *_: (_ for _ in ()).throw(TimeoutError('30-second diagnostic limit')))
    signal.alarm(30)
    counts = Counter()
    for phase in (algebra_controls, augmented_controls, recolouring_controls,
                  reading_controls, return_controls):
        phase(counts)
    signal.alarm(0)
    require(counts['no_g_plus_k_equals_ell_assumption'] > 0, 'independence tests are nonvacuous')
    return {'status': 'PASS', 'scope': 'bounded finite typed triangle-table/action diagnostics',
            'original_exact_menus': len(EXACT), 'augmented_menus': len(AUGMENTED),
            'counts': dict(sorted(counts.items())),
            'seconds': round(time.monotonic() - START, 3),
            'limits': 'No infinite-source, actual finite-kernel, SAP/CCO/primitivity, HKN or EPPA certification.'}


if __name__ == '__main__':
    print(json.dumps(check(), sort_keys=True))
