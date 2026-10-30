#!/usr/bin/env python3
"""Bounded B039 diagnostics for unary frames and actual quotient fibres.

No finite permutation action has an infinite orbit. These controls test
the finite identities used in the proofs and bounded avoidance instances
with explicit spare representatives; they never substitute a large finite
index for the theorem's INFINITE relative index. Actual unary closures,
pointwise stabilisers, equivariant term functions and quotient-fibre
images are computed independently. Missing named factorisation and a
finite proper relative index have distinct off-closure witnesses.

The exhaustive closure tests include zero generators and two total unary
functions on at most three points. Product actions test simultaneous
avoidance of several different term values by ONE representative.
Separate equivalence-fibre structures exhaust finite closed A <= B and
record exactly when the finite reservoir runs out. No SAP, homogeneity,
infinite avoidance, relative-kernel theorem or Lean proof is certified.
Reproduce: timeout 10s python tools/check_unary_fresh_frames_controls.py
"""
from collections import Counter
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


def subsets(xs, limit=None):
    xs = tuple(xs)
    for size in range(min(len(xs), len(xs) if limit is None else limit) + 1):
        for values in combinations(xs, size):
            yield frozenset(values)


def closure(seed, functions):
    """Typed functions are dictionaries; no omitted values on their sorts."""
    current = frozenset(seed)
    while True:
        following = current | frozenset(f[x] for f in functions for x in current if x in f)
        if following == current:
            return current
        current = following


def unary_terms(n, functions):
    identity = tuple(range(n))
    terms = {identity}
    frontier = [identity]
    while frontier:
        term = frontier.pop()
        for f in functions:
            following = tuple(f[term[x]] for x in range(n))
            if following not in terms:
                terms.add(following)
                frontier.append(following)
    return tuple(sorted(terms))


def exhaustive_unary_identities(counts):
    for n in range(4):
        all_maps = tuple(product(range(n), repeat=n))
        for functions in product(all_maps, repeat=2):
            dictionaries = tuple(dict(enumerate(f)) for f in functions)
            closures = {s: closure(s, dictionaries) for s in subsets(range(n))}
            group = tuple(g for g in permutations(range(n))
                          if all(g[f[x]] == f[g[x]] for f in functions for x in range(n)))
            counts['total_two_unary_structures'] += 1
            require(closures[frozenset()] == frozenset(), 'no nullary generators: empty closure is empty')
            for seed, generated in closures.items():
                union = frozenset().union(*(closures[frozenset({x})] for x in seed))
                require(generated == union, 'unary closure is exactly the union of singleton closures')
                seed_stabiliser = tuple(g for g in group if all(g[x] == x for x in seed))
                closed_stabiliser = tuple(g for g in group if all(g[x] == x for x in generated))
                require(seed_stabiliser == closed_stabiliser,
                        'pointwise stabiliser of generators equals stabiliser of their ACTUAL closure')
                for g in group:
                    require(closure({g[x] for x in seed}, dictionaries) == {g[x] for x in generated},
                            'closure commutes with actual automorphisms')
                    counts['closure_equivariance_checks'] += 1
                counts['closure_union_and_stabiliser_checks'] += 1
            if n and {g[0] for g in group} == set(range(n)):
                terms = unary_terms(n, functions)
                require(len({term[0] for term in terms}) == len(terms),
                        'under transitivity one value determines an entire equivariant term function')
                require(len(terms) == len(closures[frozenset({0})]),
                        'distinct term FUNCTIONS are bounded by singleton closure, regardless of syntax')
                for term in terms:
                    require(all(term[g[x]] == g[term[x]] for g in group for x in range(n)),
                            'all generated term functions are equivariant')
                counts['transitive_term_function_models'] += 1
                counts['distinct_transitive_term_functions'] += len(terms)
        tick()


def swap(size, a, b):
    return tuple(b if x == a else a if x == b else x for x in range(size))


def product_fibre_model(q, width):
    real = tuple(('M', i, j) for i in range(q) for j in range(width))
    quot = tuple(('Q', i) for i in range(q))
    coord = tuple(('U', j) for j in range(width))
    forced = tuple(('V', i) for i in range(q))
    p = {x: ('Q', x[1]) for x in real}
    t = {x: ('U', x[2]) for x in real}
    s = {x: ('V', x[1]) for x in quot}
    terms = (dict(zip(real, real)), p, t, {x: s[p[x]] for x in real})
    return real, quot, real + quot + coord + forced, (p, t, s), terms


def product_action(x, outer, inner):
    if x[0] == 'M':
        return ('M', outer[x[1]], inner[x[2]])
    if x[0] == 'U':
        return ('U', inner[x[1]])
    return (x[0], outer[x[1]])


def product_fibre_controls(counts, witnesses):
    for width in range(2, 8):
        real, quot, host, functions, terms = product_fibre_model(2, width)
        p, _, _ = functions
        named_quotient_terms = (dict(zip(quot, quot)), functions[2])
        for term in terms:
            j_le_k = all(p[x] != p[y] or term[x] == term[y] for x, y in product(real, repeat=2))
            named_factor = any(all(term[x] == sigma[p[x]] for x in real)
                               for sigma in named_quotient_terms)
            require(j_le_k == named_factor,
                    'positive sample has literal global named-term factorisation, not just a set-theoretic map')
            counts['literal_named_factorisation_checks'] += 1
        for b in quot:
            fibre = tuple(x for x in real if p[x] == b)
            for first, second in product(fibre, repeat=2):
                outer, inner = tuple(range(2)), swap(width, first[2], second[2])
                require(product_action(b, outer, inner) == b and
                        product_action(first, outer, inner) == second,
                        'actual quotient stabiliser is transitive on the ENTIRE actual fibre')
                counts['actual_fibre_transitivity_witnesses'] += 1
            forced = []
            unforced = []
            for term in terms:
                values = {term[x] for x in fibre}
                relative_index = len(values)
                kernel_inclusion = all(term[x] == term[y] for x, y in product(fibre, repeat=2))
                require(kernel_inclusion == (relative_index == 1),
                        'actual J <= K is exactly constancy on the actual J fibre')
                # Partition fibre by the ACTUAL term kernel, not a declared lattice label.
                pieces = {frozenset(y for y in fibre if term[y] == term[x]) for x in fibre}
                require(len(pieces) == relative_index, '[J:J intersection K] counts actual term values')
                if kernel_inclusion:
                    require(values <= closure({b}, functions),
                            'in this positive sample each forced term has a named factor value')
                    forced.append(term)
                else:
                    require(relative_index == width, 'sample unforced indices grow with fibre width')
                    unforced.append(term)
                counts['actual_kernel_and_relative_index_checks'] += 1
            require(len(forced) == len(unforced) == 2, 'identity and coordinate term must BOTH be avoided')
            # Bound the forbidden set strictly below the finite fibre width.
            for forbidden in subsets(host, min(2, width - 1)):
                good = tuple(x for x in fibre if all(term[x] not in forbidden for term in unforced))
                require(good, 'one representative simultaneously avoids every unforced term', forbidden)
                x = good[0]
                require(closure({x}, functions) & forbidden == closure({b}, functions) & forbidden,
                        'closure intersection retains exactly the named FORCED values')
                require(x not in forbidden, 'the real identity term is itself unforced')
                outer, inner = tuple(range(2)), swap(width, 0, x[2])
                require(product_action(('M', b[1], 0), outer, inner) == x and
                        all(product_action(term[('M', b[1], 0)], outer, inner) == term[x]
                            for term in unforced),
                        'ONE stabiliser element moves all unforced values together')
                counts['simultaneous_bounded_avoidance_instances'] += 1
        # Successive choices retain a growing forbidden set of all earlier
        # representatives AND their unforced coordinate values.
        if width >= 4:
            for sequence in product(quot, repeat=3):
                for initial in subsets(host, 1):
                    forbidden = set(initial)
                    chosen = []
                    for b in sequence:
                        fibre = tuple(x for x in real if p[x] == b)
                        unforced = (terms[0], terms[2])
                        x = next((x for x in fibre if all(t[x] not in forbidden for t in unforced)), None)
                        require(x is not None, 'bounded successive fibre choices have sufficient spare width')
                        require(closure({x}, functions) & forbidden == closure({b}, functions) & forbidden,
                                'successive choice preserves the same forced intersection invariant')
                        chosen.append(x)
                        forbidden.update(t[x] for t in unforced)
                        counts['successive_representative_choices'] += 1
                    require(len(set(chosen)) == len(chosen), 'successive representatives are pairwise distinct')
        tick()
    # Individual avoidability does not imply a COMMON representative if
    # infinite-orbit avoidance is replaced by arbitrary finite indices.
    real, _, _, _, terms = product_fibre_model(1, 2)
    forbidden = {real[0], ('U', 1)}
    require(all(any(t[x] not in forbidden for x in real) for t in (terms[0], terms[2])) and
            not any(all(t[x] not in forbidden for t in (terms[0], terms[2])) for x in real),
            'two separately avoidable finite orbits can have no simultaneous avoiding point')
    witnesses['finite_separate_avoidance_is_not_simultaneous'] = {
        'fibre_size': 2, 'forbidden': [list(x) for x in sorted(forbidden)],
        'each_unforced_term_individually_avoidable': True,
        'common_representative_exists': False}


def frame_model(width):
    real = tuple(('M', i, j) for i in range(2) for j in range(width))
    q = tuple(('Q', i) for i in range(2))
    v = tuple(('V', i) for i in range(2))
    p = {x: ('Q', x[1]) for x in real}
    s = {x: ('V', x[1]) for x in q}
    inverse = {x: ('Q', x[1]) for x in v}
    return real, real + q + v, (p, s, inverse)


def fresh_frame_controls(counts, witnesses):
    for width in (2, 3, 4):
        real, host, functions = frame_model(width)
        closed = tuple(s for s in subsets(host) if closure(s, functions) == s)
        for a in closed:
            for b in closed:
                if not a <= b:
                    continue
                d = set(a) & set(real)
                impossible = False
                for i in range(2):
                    if ('Q', i) not in a or any(x[1] == i for x in d):
                        continue
                    spare = next((x for x in real if x[1] == i and x not in b), None)
                    if spare is None:
                        impossible = True
                        break
                    d.add(spare)
                if impossible:
                    # Any real generator of that hidden quotient is in B\A.
                    # Hence this is actual exhaustion, not a failed search.
                    require(any(('Q', i) in a and not any(x in a for x in real if x[1] == i)
                                and all(x in b for x in real if x[1] == i) for i in range(2)),
                            'finite frame failure has a completely exhausted required fibre')
                    counts['finite_reservoir_exhaustion_instances'] += 1
                    continue
                generated = closure(d, functions)
                require(a <= generated and generated & b == a,
                        'literal real frame generates all A and separates its closure from B minus A')
                require(generated == frozenset().union(*(closure({x}, functions) for x in d)),
                        'the frame construction uses ONLY a union of singleton closures')
                counts['literal_closed_base_fresh_frames'] += 1
        tick()
    witnesses['finite_models_do_not_have_infinite_reservoirs'] = {
        'example': 'one hidden quotient in A, every real point of its finite fibre in B',
        'fresh_frame_exists': False,
        'consequence': 'bounded positive samples do not certify infinite orbit or index assumptions'}


def local_failure_controls(counts, witnesses):
    # Two named projections have equal actual kernels, but no function
    # starts at Q. Set-theoretic factorisation exists; a named term does not.
    real = tuple(('M', i, j) for i in range(2) for j in range(2))
    q = tuple(('Q', i) for i in range(2))
    v = tuple(('V', i) for i in range(2))
    p = {x: ('Q', x[1]) for x in real}
    tau = {x: ('V', x[1]) for x in real}
    functions = (p, tau)
    base, value = q[0], v[0]
    group = []
    for outer in permutations(range(2)):
        for inner0, inner1 in product(tuple(permutations(range(2))), repeat=2):
            def action(x):
                if x[0] == 'M':
                    return ('M', outer[x[1]], (inner0, inner1)[x[1]][x[2]])
                return (x[0], outer[x[1]])
            image = {x: action(x) for x in real + q + v}
            require(all(image[f[x]] == f[image[x]] for f in functions for x in f),
                    'missing-factor witness group really preserves BOTH named projections')
            group.append(image)
    stabiliser = tuple(g for g in group if g[base] == base)
    require(all(g[value] == value for g in stabiliser) and value not in closure({base}, functions),
            'a forced fibre value is fixed over b while absent from its named unary closure')
    require(all(p[x] != p[y] or tau[x] == tau[y] for x, y in product(real, repeat=2)),
            'missing named factor occurs despite literal kernel inclusion')
    fibre_values = {tau[x] for x in real if p[x] == base}
    require(fibre_values == {value} and closure({base}, functions) == {base},
            'unique definable fibre value is not manufactured into a nonexistent named term')
    witnesses['kernel_inclusion_without_named_factor'] = {
        'J_le_K': True, 'unique_fibre_value': list(value),
        'closure_of_base': [list(x) for x in sorted(closure({base}, functions))],
        'value_fixed_by_full_sample_base_stabiliser': True,
        'named_Q_to_V_term_exists': False,
        'defining_formula': 'exists x (p(x)=b and tau(x)=v)',
        'set_theoretic_factor_exists': True}
    # Finite PROPER relative index: the fibre image is a finite invariant
    # set with a nontrivial stabiliser orbit, disjoint from term closure.
    real, quot, _, functions, terms = product_fibre_model(2, 3)
    base = quot[0]
    values = {terms[2][x] for x in real if functions[0][x] == base}
    orbit = {product_action(('U', 0), (0, 1), inner) for inner in permutations(range(3))}
    require(values == orbit and len(values) == 3 and not values & closure({base}, functions),
            'finite proper actual index gives a finite nontrivial orbit outside named closure')
    witnesses['finite_proper_relative_index'] = {
        'relative_index': len(values), 'base_stabiliser_orbit_size': len(orbit),
        'all_fibre_image_values_outside_named_base_closure': True,
        'some_base_stabiliser_element_moves_each_value': True,
        'local_failure': 'algebraic off-closure values; infinite-index condition fails'}
    # A constant is exactly why the no-nullary-generator gate matters.
    seed = frozenset()
    with_constant = closure(seed | {0}, ({0: 0, 1: 1},))
    singleton_union = frozenset().union(*(closure({x}, ({0: 0, 1: 1},)) for x in seed))
    require(with_constant != singleton_union, 'a nullary generator defeats the empty union identity')
    witnesses['nullary_generator_boundary'] = {
        'constant': 0, 'closure_of_empty': sorted(with_constant),
        'union_of_no_singleton_closures': sorted(singleton_union)}
    # An action subgroup has its OWN stabiliser orbits. This finite
    # illustration does not claim SAP for a bounded finite age.
    full_group = tuple(permutations(range(3)))
    proper_group = tuple(g for g in full_group if g[0] == 0)
    require(len({g[0] for g in full_group}) == 3 and {g[0] for g in proper_group} == {0},
            'full-group and proper-subgroup orbit assertions are distinct')
    witnesses['proper_subgroup_orbits_are_separate'] = {
        'full_sample_orbit_size': 3, 'proper_subgroup_orbit_size': 1,
        'SAP_claimed_for_finite_sample_age': False}
    counts['local_failure_and_scope_witnesses'] += len(witnesses)
    tick()


def main():
    counts, witnesses = Counter(), {}
    exhaustive_unary_identities(counts)
    product_fibre_controls(counts, witnesses)
    fresh_frame_controls(counts, witnesses)
    local_failure_controls(counts, witnesses)
    print(json.dumps(dict(status='PASS', scope='bounded unary closure, quotient-fibre and real-frame diagnostics',
                          seconds=round(time.monotonic() - START, 3), counts=dict(sorted(counts.items())),
                          witnesses=witnesses,
                          limits='All sampled actions are finite: no infinite orbit/index premise, homogeneous hereditary SAP equivalence, general group avoidance theorem or Lean proof is certified.'),
                     sort_keys=True))


if __name__ == '__main__':
    signal.alarm(30)
    main()
