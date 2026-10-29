#!/usr/bin/env python3
"""Bounded B035 full-code diagnostics, not all-size theorem certificates.

The main models have one partial idempotent unary function (normal forms
id,F), an arbitrary unary predicate and a directed binary relation. All
such models on at most two points are used as source hosts. Roots include
empty tuples, scalars, arbitrary pairs, relation-selected pairs and
function-graph pairs. Every source root subset of size at most two is
checked against fixed small target samples, including its own host.
Hidden and visible embeddings are enumerated independently. Domain
reflection is mandatory; all same-root and cross-root code instances are
retained. There is no quotient of root tuples.

Separate checks exercise color transport in a genuine finite ordered
Ramsey instance, ambient root-cover cofinality, same-host expansion
reconstruction, and concrete missing-code/reduct-commutation boundaries.
The final EP incidence controls check logical quantifiers only: they are
NOT counterexamples satisfying every structural hypothesis of the theorem.
No arbitrary many-sorted language, Ramsey/EP transfer theorem, infinite
ambient source or Lean implementation is certified. Normal runtime <10s;
hard deadline 30s. Reproduce: timeout 10s python tools/check_full_code_controls.py
"""
from collections import Counter
from itertools import combinations, product
import json
import signal
import time


START = time.monotonic()


def require(test, message, witness=None):
    if not test:
        raise AssertionError((message, witness))


def tick():
    require(time.monotonic() - START < 30, '30-second diagnostic deadline')


def points(mask):
    return tuple(i for i in range(mask.bit_length()) if mask & (1 << i))


class Model:
    def __init__(self, f, unary=0, relation=0, roots=None):
        self.f = tuple(f)
        self.n = len(f)
        self.unary, self.relation = unary, relation
        require(all(y < 0 or self.f[y] == y for y in f), 'F squared equals F as a partial map')
        self.roots = tuple(self.valid_roots() if roots is None else roots)
        self.lookup = {r: i for i, r in enumerate(self.roots)}
        require(len(self.lookup) == len(self.roots), 'tagged tuple roots have no extra quotient')
        self.values = tuple(tuple(v for x in coords for v in (x, self.f[x]))
                            for _, coords in self.roots)
        self.unary_code = tuple((tag, tuple(v >= 0 for v in vals),
                                 tuple(v >= 0 and bool(unary & (1 << v)) for v in vals))
                                for (tag, _), vals in zip(self.roots, self.values))
        self.binary_code = tuple(tuple((
            tuple(x >= 0 and y >= 0 and x == y for x in xs for y in ys),
            tuple(x >= 0 and y >= 0 and self.rel(x, y) for x in xs for y in ys))
            for ys in self.values) for xs in self.values)

    def rel(self, x, y):
        return bool(self.relation & (1 << (self.n * x + y)))

    def valid_roots(self):
        yield ('z', ())  # a valid empty root tuple
        for x in range(self.n):
            yield ('v', (x,))
        for x, y in product(range(self.n), repeat=2):
            yield ('p', (x, y))
            if x != y and self.rel(x, y):
                yield ('q', (x, y))
            if x != y and self.f[x] == y:
                yield ('f', (x, y))

    def closure(self, mask):
        result = mask
        for x in points(mask):
            if self.f[x] >= 0:
                result |= 1 << self.f[x]
        return result

    def support(self, roots):
        seed = 0
        for i in roots:
            for x in self.roots[i][1]:
                seed |= 1 << x
        return self.closure(seed)

    def bit(self, a, i, b, j, relation=False):
        return self.binary_code[a][b][int(relation)][i * len(self.values[b]) + j]


def hidden_embeddings(source, support, target):
    domain = points(support)
    answer = []
    if len(domain) > target.n:
        return answer
    for image in product(range(target.n), repeat=len(domain)):
        if len(set(image)) != len(image):
            continue
        mapping = dict(zip(domain, image))
        if any((source.f[x] < 0) != (target.f[mapping[x]] < 0) or
               (source.f[x] >= 0 and mapping[source.f[x]] != target.f[mapping[x]]) or
               bool(source.unary & (1 << x)) != bool(target.unary & (1 << mapping[x]))
               for x in domain):
            continue
        if any(source.rel(x, y) != target.rel(mapping[x], mapping[y])
               for x, y in product(domain, repeat=2)):
            continue
        answer.append(mapping)
    return answer


def induced_root_map(source, roots, target, mapping):
    return tuple(target.lookup[(source.roots[i][0],
                                tuple(mapping[x] for x in source.roots[i][1]))]
                 for i in roots)


def visible_embeddings(source, roots, target):
    choices = tuple(tuple(j for j, sig in enumerate(target.unary_code)
                          if sig == source.unary_code[i]) for i in roots)
    result = []
    for image in product(*choices):
        if len(set(image)) != len(image):
            continue
        if all(source.binary_code[a][b] == target.binary_code[image[i]][image[j]]
               for i, a in enumerate(roots) for j, b in enumerate(roots)):
            result.append(image)
    return result


def lift_root_map(source, roots, target, image):
    result = {}
    for a, b in zip(roots, image):
        for x, y in zip(source.values[a], target.values[b]):
            if x >= 0:
                require(y >= 0, 'definedness reflects in visible embedding')
                require(x not in result or result[x] == y, 'cross-root equality makes lift well-defined')
                result[x] = y
    require(len(set(result.values())) == len(result), 'full equality code makes lift injective')
    return result


def reconstruction(source, roots, counts):
    # Reconstruct the quotient and its F/U/R diagram using only recorded
    # code bits. Actual values are used only afterwards for comparison.
    presentations = [(a, t) for a in roots for t in range(len(source.values[a]))
                     if source.unary_code[a][1][t]]
    representatives, classes = [], {}
    for p in presentations:
        a, t = p
        matching = [k for k, (b, u) in enumerate(representatives) if source.bit(a, t, b, u)]
        if matching:
            require(len(matching) == 1, 'equality codes give a single quotient class')
            classes[p] = matching[0]
        else:
            classes[p] = len(representatives)
            representatives.append(p)
    actual = [source.values[a][t] for a, t in representatives]
    require(len(set(actual)) == len(actual) and set(actual) == set(points(source.support(roots))),
            'defined presentations quotient is precisely the generated support')
    for a, t in presentations:
        require(actual[classes[(a, t)]] == source.values[a][t], 'all aliases are identified literally')
    for k, (a, t) in enumerate(representatives):
        next_term = t | 1  # NF(F o id)=F and NF(F o F)=F
        f_class = classes[(a, next_term)] if source.unary_code[a][1][next_term] else -1
        f_value = actual[f_class] if f_class >= 0 else -1
        require(f_value == source.f[actual[k]], 'normal-form composition recovers domains and values')
        require(source.unary_code[a][2][t] == bool(source.unary & (1 << actual[k])),
                'unary code reconstructs the actual predicate')
        for ell, (b, u) in enumerate(representatives):
            require(source.bit(a, t, b, u, True) == source.rel(actual[k], actual[ell]),
                    'binary and same-root codes reconstruct all relation instances')
    counts['reconstructed_generated_diagrams'] += 1
    counts['defined_coordinate_presentations'] += len(presentations)
    counts['identified_alias_presentations'] += len(presentations) - len(representatives)


def all_models():
    for n in range(3):
        for f in product(range(-1, n), repeat=n):
            if not all(y < 0 or f[y] == y for y in f):
                continue
            for unary in range(1 << n):
                for relation in range(1 << (n * n)):
                    yield Model(f, unary, relation)


def shifted_orphan_extension(source):
    f = (-1,) + tuple(y + 1 if y >= 0 else -1 for y in source.f)
    unary = source.unary << 1
    n = source.n + 1
    relation = sum(1 << (n * (x + 1) + y + 1) for x, y in product(range(source.n), repeat=2)
                   if source.rel(x, y))
    return Model(f, unary, relation)


def embedding_controls(counts):
    models = list(all_models())
    small = [m for m in models if m.n <= 1]
    large = [m for m in models if m.n == 2]
    for index, source in enumerate(models):
        counts['actual_partial_idempotent_models'] += 1
        targets = small + [source, large[(index * 17 + 11) % len(large)]]
        extended = shifted_orphan_extension(source)
        shift = {x: x + 1 for x in range(source.n)}
        for size in range(3):
            for roots in combinations(range(len(source.roots)), size):
                reconstruction(source, roots, counts)
                support = source.support(roots)
                for target in targets:
                    left = visible_embeddings(source, roots, target)
                    hidden = hidden_embeddings(source, support, target)
                    right = [induced_root_map(source, roots, target, g) for g in hidden]
                    require(len(right) == len(set(right)) and set(left) == set(right),
                            'FCODE actual embedding sets are in bijection', (source.f, roots, target.f))
                    for image in left:
                        lifted = lift_root_map(source, roots, target, image)
                        require(lifted in hidden, 'reconstructed map is an actual domain-reflecting embedding')
                        require(induced_root_map(source, roots, target, lifted) == image,
                                'root map and hidden lift are mutual inverses')
                        counts['mutual_inverse_embedding_checks'] += 1
                    counts['embedding_set_comparisons'] += 1
                # A nontrivial relabeling into a larger actual host checks
                # functorial composition, not only an identity map.
                for image in visible_embeddings(source, roots, source):
                    lifted = lift_root_map(source, roots, source, image)
                    root_composite = tuple(extended.lookup[(source.roots[i][0],
                                            tuple(x + 1 for x in source.roots[i][1]))] for i in image)
                    hidden_composite = {x: shift[y] for x, y in lifted.items()}
                    require(induced_root_map(source, roots, extended, hidden_composite) == root_composite,
                            'FCODE commutes with actual hidden composition')
                    require(root_composite in visible_embeddings(source, roots, extended),
                            'composition remains an induced full-code embedding')
                    counts['nonidentity_naturality_checks'] += 1
        tick()


def ramsey_controls(counts):
    ordered = lambda n: Model(tuple(range(n)), (1 << n) - 1,
                              sum(1 << (n * x + y) for x in range(n) for y in range(x + 1, n)))
    a, b, d = (ordered(n) for n in (1, 2, 3))
    roots_a = (a.lookup[('v', (0,))],)
    roots_b = tuple(range(len(b.roots)))
    a_to_b = visible_embeddings(a, roots_a, b)
    a_to_d = visible_embeddings(a, roots_a, d)
    b_to_d = hidden_embeddings(b, b.support(roots_b), d)
    require(len(a_to_d) == 3 and len(a_to_b) == 2 and len(b_to_d) == 3,
            'actual ordered Ramsey A=1 B=2 D=3 embedding sets')
    index = {image: i for i, image in enumerate(a_to_d)}
    for colors in product(range(2), repeat=len(a_to_d)):
        successful = []
        for g in b_to_d:
            root_g = induced_root_map(b, roots_b, d, g)
            restricted = [tuple(root_g[i] for i in emb) for emb in a_to_b]
            hidden_readout = []
            for emb in a_to_b:
                h = lift_root_map(a, roots_a, b, emb)
                composite = {x: g[y] for x, y in h.items()}
                hidden_readout.append(induced_root_map(a, roots_a, d, composite))
            require(restricted == hidden_readout, 'color transport agrees under all lifted embeddings')
            if len({colors[index[e]] for e in restricted}) == 1:
                successful.append(g)
            counts['Ramsey_naturality_color_readouts'] += 1
        require(successful, 'finite ordered hidden arrow yields visible monochromatic copy')
        counts['two_color_Ramsey_instance_colorings'] += 1


def ambient_roots(model, carrier):
    # This different QF interpretation intentionally allows orphan points
    # in proper induced closed substructures of a root-covered ambient P.
    result = [('z', ())]
    for x in carrier:
        if model.unary & (1 << x):
            result.append(('v', (x,)))
        for y in carrier:
            if x != y and model.f[x] == y:
                result.append(('f', (x, y)))
    return tuple(result)


def root_cover_controls(counts, witnesses):
    cases = list(all_models())
    cases += [Model((1, 1, -1), 5), Model((1, 1, 2), 1), Model((1, 1, 1), 1)]
    witnessed_growth = False
    for ambient in cases:
        all_points = (1 << ambient.n) - 1
        roots = ambient_roots(ambient, range(ambient.n))
        cover = {}
        for root in roots:
            for x in root[1]:
                cover.setdefault(x, root)
                if ambient.f[x] >= 0:
                    cover.setdefault(ambient.f[x], root)
        if set(cover) != set(range(ambient.n)):
            counts['ambient_models_rejected_by_root_cover'] += 1
            continue
        counts['ambient_root_covered_models'] += 1
        for d in range(1 << ambient.n):
            if ambient.closure(d) != d:
                continue
            chosen = {cover[z] for z in points(d)}
            coordinates = 0
            for _, coords in chosen:
                for x in coords:
                    coordinates |= 1 << x
            e = ambient.closure(coordinates)
            valid_in_e = ambient_roots(ambient, points(e))
            require(all(r in valid_in_e for r in chosen), 'QF root validity restricts to closed induced E')
            require(d & e == d and ambient.closure(e) == e, 'constructed same E is closed and contains D')
            generated = 0
            for _, coords in valid_in_e:
                for x in coords:
                    generated |= 1 << x
            generated = ambient.closure(generated)
            require(generated == e, 'the SAME constructed E equals h(N(E))')
            require(e.bit_count() <= 2 * coordinates.bit_count(), 'finite normal-form bound makes E finite')
            if e != d:
                witnessed_growth = True
            counts['cofinal_same_E_constructions'] += 1
    require(witnessed_growth, 'cofinal construction genuinely enlarges a closed orphan-only D')
    p = Model((1, 1), 1)
    roots_d = ambient_roots(p, (1,))
    require(roots_d == (('z', ()),), 'closed D={1} has no nonempty valid roots internally')
    witnesses['ambient_root_cover_can_require_growth'] = {
        'ambient_function': [1, 1], 'unary_root_predicate': [0], 'closed_D': [1],
        'internal_generated_support_of_D': [], 'chosen_root': [0], 'constructed_E': [0, 1]}


def code_signature(model, roots):
    return (tuple(model.unary_code[i] for i in roots),
            tuple(model.binary_code[i][j] for i in roots for j in roots))


def same_host_controls(counts, witnesses):
    def fixed_tag_roots(n):
        return tuple([('z', ())] + [('v', (x,)) for x in range(n)] +
                     [('p', (x, y)) for x, y in product(range(n), repeat=2)])

    for f in ((-1, -1), (1, 1), (0, 1)):
        # These tags and validity are fixed in the UNEXPANDED language.
        fixed_roots = fixed_tag_roots(2)
        signatures = {}
        for unary in range(4):
            for relation in range(16):
                expanded = Model(f, unary, relation, fixed_roots)
                roots = tuple(range(len(fixed_roots)))
                require(expanded.support(roots) == 3, 'positive same-host E is fully root generated')
                signature = code_signature(expanded, roots)
                require(signature not in signatures, 'full code uniquely determines expansion on the SAME fixed E')
                signatures[signature] = (unary, relation)
                bigger = shifted_orphan_extension(expanded)
                shifted = Model(bigger.f, bigger.unary, bigger.relation, fixed_tag_roots(bigger.n))
                embedded_roots = induced_root_map(expanded, roots, shifted, {0: 1, 1: 2})
                require(code_signature(shifted, embedded_roots) == signature,
                        'an unrelated representation has the same full root code')
                reconstruction(shifted, embedded_roots, counts)
                require(shifted.support(embedded_roots) == 6,
                        'generated expanded support has precisely the canonical template vertices')
                transported_unary = sum(1 << x for x in range(2) if shifted.unary & (1 << (x + 1)))
                transported_relation = sum(1 << (2 * x + y) for x, y in product(range(2), repeat=2)
                                            if shifted.rel(x + 1, y + 1))
                require((transported_unary, transported_relation) == (unary, relation),
                        'transport realizes the visible expansion on the original E')
                counts['same_host_lift_and_uniqueness_checks'] += 1
    # Without h(N(E))=E a root-invisible orphan supports undetected data.
    root = (('v', (0,)),)
    first, second = Model((-1, -1), 1, 0, root), Model((-1, -1), 1, 8, root)
    require(code_signature(first, (0,)) == code_signature(second, (0,)) and
            first.support((0,)) == 1 and first.relation != second.relation,
            'orphan relation is invisible when full-root-host gate is omitted')
    witnesses['orphan_prevents_same_host_uniqueness_without_gate'] = {
        'E': [0, 1], 'root_coordinates': [0], 'h_N_E': [0],
        'differing_expanded_relation': [1, 1], 'same_full_visible_code': True,
        'violated_gate': 'h(N(E))=E'}
    # Added functions may enlarge expanded closure, so forgetting its
    # expansion need not recover the unexpanded one-generated template.
    old_closure = {0}
    added_g = (1, 1)
    expanded_closure = {0, added_g[0]}
    same_host_g_choices = (-1, 0)
    code_at_root = lambda value: (value >= 0, value == 0)
    desired = code_at_root(added_g[0])
    require(expanded_closure != old_closure and all(code_at_root(v) != desired for v in same_host_g_choices),
            'added-function full code has no lift on the smaller unexpanded template')
    witnesses['added_function_breaks_reduct_closure_commutation'] = {
        'unexpanded_template': [0], 'expanded_generated_support': [0, 1], 'added_g': [1, 1],
        'root_code': {'g_defined': True, 'g_equals_identity': False},
        'same_singleton_host_lift_exists': False, 'violated_gate': 'reduct of h(B^o) equals h(B)'}
    counts['same_host_missing_gate_witnesses'] += 2


def missing_code_controls(counts, witnesses):
    # A full code, not its root metadata alone, controls partial domains.
    source = Model((-1,), roots=(('v', (0,)),))
    target = Model((1, 1), roots=(('v', (0,)),))
    source_e, target_e = source.binary_code[0][0][0], target.binary_code[0][0][0]
    require(source_e[:3] == target_e[:3] and source_e[3] != target_e[3],
            'only E_F,F distinguishes undefined F from a distinct fixed output on this root')
    require(source.unary_code[0][0::2] == target.unary_code[0][0::2],
            'tags and ordinary unary predicate codes agree')
    require(not visible_embeddings(source, (0,), target), 'full definedness code rejects a false hidden embedding')
    witnesses['missing_definedness'] = {
        'source_F': [-1], 'target_F': [1, 1], 'root': [0],
        'E_id_F_in_both': False, 'E_F_F_source': False, 'E_F_F_target': True,
        'omitted_information': 'definedness bits including E_F,F; all ordinary predicates empty'}
    # Within-root aliases are invisible if every same-root equality code
    # is dropped, even though coordinate definedness remains recorded.
    source = Model((-1, -1), roots=(('p', (0, 0)),))
    target = Model((-1, -1), roots=(('p', (0, 1)),))
    require(source.unary_code == target.unary_code and
            source.binary_code[0][0][1] == target.binary_code[0][0][1] and
            source.binary_code[0][0][0] != target.binary_code[0][0][0],
            'missing same-root equality permits changing a repeated coordinate')
    witnesses['missing_within_root_equality'] = {'source_root': [0, 0], 'target_root': [0, 1],
                                               'full_code_accepts_map': False}
    # Root injectivity does not imply injectivity of all hidden coordinates.
    source = Model((-1, -1), roots=(('v', (0,)), ('p', (1, 1))))
    target = Model((-1,), roots=(('v', (0,)), ('p', (0, 0))))
    require(source.unary_code == target.unary_code and
            all(source.binary_code[i][i] == target.binary_code[i][i] for i in range(2)) and
            all(source.binary_code[i][j][1] == target.binary_code[i][j][1] for i, j in product(range(2), repeat=2)) and
            source.binary_code[0][1][0] != target.binary_code[0][1][0],
            'cross-root equality is needed despite injective tagged root map')
    witnesses['missing_cross_root_equality'] = {'source_roots': [['v', [0]], ['p', [1, 1]]],
                                               'target_roots': [['v', [0]], ['p', [0, 0]]],
                                               'root_map_injective': True, 'hidden_lift_injective': False}
    roots = (('p', (0, 1)),)
    first, second = Model((-1, -1), relation=2, roots=roots), Model((-1, -1), relation=4, roots=roots)
    require(first.unary_code == second.unary_code and first.binary_code[0][0][0] == second.binary_code[0][0][0]
            and first.binary_code[0][0][1] != second.binary_code[0][0][1],
            'opposite strict orders have equal non-comparison root codes')
    witnesses['missing_same_root_comparison'] = {'root': [0, 1], 'source_order': [[0, 1]],
                                                'target_order': [[1, 0]], 'full_code_accepts_identity': False}
    counts['missing_code_witnesses'] += 4


def normalized_witness_restriction_controls(counts, witnesses):
    # This is a guard on one EP proof step, not a counterexample to its
    # final transfer theorem. Added functions can make an arbitrary
    # unexpanded induced D nonclosed even when every ROOT-GENERATED
    # support still commutes with forgetting the expansion.
    e, d = {0, 1, 2}, {1, 2}
    unary = {1}
    relation = {(0, 2)}
    g = (0, 1, 0)

    def roots(carrier):
        return tuple([('z', ())] + [('v', (x,)) for x in sorted(carrier) if x in unary] +
                     [('p', (x, y)) for x, y in sorted(relation) if x in carrier and y in carrier])

    def coordinates(root_set):
        return {x for _, args in root_set for x in args}

    def g_closure(seed):
        current = set(seed)
        while True:
            following = current | {g[x] for x in current}
            if following == current:
                return current
            current = following

    roots_e, roots_d = roots(e), roots(d)
    d0 = coordinates(roots_d)  # no unexpanded functions in this example
    require(coordinates(roots_e) == e, 'the original E is fully root-generated')
    require(g_closure(d) != d and g[2] == 0 and 0 not in d,
            'an arbitrary unexpanded induced D need not be closed under an added function')
    require(d0 == {1} and roots(d0) == roots_d and g_closure(d0) == d0,
            'D0=h(N(D)) removes orphans, preserves N(D), and is expanded-closed')
    for size in range(len(roots_e) + 1):
        for chosen in combinations(roots_e, size):
            support = coordinates(chosen)
            require(g_closure(support) == support,
                    'all root-generated supports commute with forgetting the added unary function')
            counts['normalized_witness_support_commutation_checks'] += 1
    witnesses['normalize_EP_witness_before_expanded_restriction'] = {
        'kind': 'restriction-step guard, not a counterexample to the final transfer theorem',
        'unexpanded_E': [0, 1, 2], 'unexpanded_functions': [],
        'root_unary_predicate': [1], 'root_binary_relation': [[0, 2]],
        'added_expanded_G': list(g), 'unexpanded_induced_D': [1, 2],
        'D_is_expanded_closed': False, 'normalized_D0': sorted(d0),
        'N_D0_equals_N_D': True, 'D0_is_expanded_closed': True,
        'all_root_generated_supports_commute_with_reduct': True}
    counts['normalized_witness_restriction_guard_checks'] += 1


def ep_quantifier_controls(counts, witnesses):
    # Finite logical incidence tables ONLY. No claim is made that these
    # tables satisfy all hidden/visible expansion hypotheses.
    one_host = {'b0': True, 'b1': False}
    require(any(one_host.values()) and not all(one_host.values()),
            'some allowed competing expansion is weaker than every competing expansion')
    incidence = {'E0': {'a0': (True, True), 'a1': (False, False)},
                 'E1': {'a0': (False, False), 'a1': (True, True)}}
    fixed_expansion_ep = all(any(all(incidence[e][a]) for e in incidence) for a in ('a0', 'a1'))
    common_host_ep = any(all(all(incidence[e][a]) for a in ('a0', 'a1')) for e in incidence)
    require(fixed_expansion_ep and not common_host_ep,
            'finite expansion types alone do not supply a common host for every source expansion')
    same_host_lifts = {'fixed_E': False, 'unrelated_E_prime': True}
    require(any(same_host_lifts.values()) and not same_host_lifts['fixed_E'],
            'a lift on some unrelated host is weaker than a lift on the fixed host')
    witnesses['EP_logical_quantifier_gates'] = {
        'kind': 'finite logical incidence diagnostics, not full structural counterexamples',
        'some_competing_expansion_suffices': False,
        'fixed_expanded_A_has_host_in_table': fixed_expansion_ep,
        'one_host_for_all_expanded_A_in_table': common_host_ep,
        'finite_source_expansion_types': 2,
        'lift_somewhere_exists': True, 'lift_on_fixed_E_exists': False}
    counts['EP_logical_quantifier_gate_checks'] += 3


def main():
    signal.signal(signal.SIGALRM, lambda *_: (_ for _ in ()).throw(TimeoutError('30-second hard deadline')))
    signal.alarm(30)
    counts, witnesses = Counter(), {}
    embedding_controls(counts)
    ramsey_controls(counts)
    root_cover_controls(counts, witnesses)
    same_host_controls(counts, witnesses)
    missing_code_controls(counts, witnesses)
    normalized_witness_restriction_controls(counts, witnesses)
    ep_quantifier_controls(counts, witnesses)
    signal.alarm(0)
    print(json.dumps(dict(status='PASS',scope='bounded partial-unary full-code reconstruction, embeddings, color transport and fixed-host diagnostics',
                         limits='Finite one-sort models and incidence tables do not certify arbitrary typed languages, infinite sources, Ramsey/EP transfer, or Lean.',
                         seconds=round(time.monotonic()-START,3),counts=dict(sorted(counts.items())),witnesses=witnesses),sort_keys=True))


if __name__ == '__main__':
    main()
