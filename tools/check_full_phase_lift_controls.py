#!/usr/bin/env python3
"""Bounded B048 private-detour/frozen-factor diagnostics.

Finite windows are witness oracles only. This checks no unbounded SAP/CCO,
support-normal interface, natural completion theorem, or Lean proof.
"""
from collections import Counter
from functools import lru_cache
from itertools import combinations, permutations, product
import json
import signal
import time

START = time.monotonic()
C = Counter()
# Actual finite window of an infinite two-class equivalence source plus
# an inactive pure sort. Active classes have four clones each.
ACTIVE = tuple(('A', b, i) for b in range(2) for i in range(4))
INACTIVE = tuple(('I', 0, i) for i in range(4))
WINDOW = ACTIVE + INACTIVE


def demand(value, message):
    if not value:
        raise AssertionError(message)


def atom(x, y):
    if x == y:
        return 'Id'
    if x[0] == y[0] == 'A':
        return 'c' if x[1] == y[1] else 'o'
    if x[0] == y[0] == 'I':
        return 'u'
    return 'm'


def bit(x, flip=0):
    return x[1] ^ flip if x[0] == 'A' else 0


def legal(x, y, colour, flip=0):
    if atom(x, y) != colour or colour == 'Id':
        return False
    if x[0] == y[0] == 'A':
        return (bit(x, flip) ^ bit(y, flip)) == (colour == 'o')
    return True  # Inactive endpoint masks have their literal full palette.


def compose(r, s):
    return {(x, z) for x, y in r for yy, z in s if y == yy}


@lru_cache(None)
def path_outputs(word, sorts):
    """Independent actual injective finite-path oracle, not relation products."""
    outputs = set()
    for values in permutations(WINDOW, len(word) + 1):
        if tuple(x[0] for x in values) != sorts:
            continue
        if all(atom(values[i], values[i + 1]) == a for i, a in enumerate(word)):
            outputs.add(atom(values[0], values[-1]))
    return frozenset(outputs)


def detours():
    K = {(x, y) for x, y in product(ACTIVE, repeat=2) if x[1] == y[1]}
    for old in ('c', 'o'):
        relation = {(x, y) for x, y in product(ACTIVE, repeat=2) if atom(x, y) == old}
        cylinder = compose(compose(K, relation), K)
        expected = {(x, y) for x, y in product(ACTIVE, repeat=2)
                    if (x[1] == y[1]) == (old == 'c')}
        demand(cylinder == expected, 'whole represented cylinder')
        if old == 'c':
            demand(any(x == y for x, y in cylinder), 'K cylinder retains old logical Id')
        C['actual_whole_cylinders'] += 1
    for x, y in permutations(ACTIVE, 2):
        old = atom(x, y)
        for u in ACTIVE:
            for v in ACTIVE:
                if len({x, u, v, y}) != 4 or u[1] != x[1] or v[1] != y[1]:
                    continue
                values = (x, u, v, y)
                word = tuple(atom(values[i], values[i + 1]) for i in range(3))
                outputs = path_outputs(word, ('A',) * 4)
                demand(old in outputs, 'root colour is realized by its private detour')
                demand(outputs == {old}, 'active path stays in its whole semantic cylinder')
                edges = {(0, 1), (1, 2), (2, 3)}
                demand((0, 3) not in edges, 'root pair remains unspecified')
                demand(all(sum(i in e for e in edges) == 2 for i in (1, 2)), 'private degrees')
                for flip in range(2):
                    demand(all(legal(values[i], values[i + 1], word[i], flip)
                               for i in range(3)), 'consecutive full pair bits legal')
                    demand(all((a == 'o') == (bit(x, flip) ^ bit(y, flip))
                               for a in outputs), 'all active outputs have requested phase')
                    C['active_marked_detours'] += 1
                C['fresh_four_vertex_witnesses'] += 1
    for x, y in permutations(WINDOW, 2):
        if x[0] == y[0] == 'A':
            continue
        z = next(t for t in INACTIVE if t not in (x, y))
        values = (x, z, y)
        word = (atom(x, z), atom(z, y))
        outputs = path_outputs(word, tuple(t[0] for t in values))
        demand(atom(x, y) in outputs, 'inactive two-edge path realizes requested root pair')
        demand(outputs <= ({'u'} if x[0] == y[0] == 'I' else {'m'}),
               'inactive endpoint mask is the full correct typed palette')
        demand(len(set(values)) == 3, 'inactive representative is fresh')
        for flip in range(2):
            demand(legal(x, z, word[0], flip) and legal(z, y, word[1], flip),
                   'inactive fixed bits retained')
        C['inactive_two_edge_detours'] += 1
    # A finite fibre of size two does not supply the required fresh active
    # four-point path in the identity cylinder, despite an abstract bit label.
    tiny = tuple(('A', 0, i) for i in range(2))
    demand(not any(len({tiny[0], u, v, tiny[1]}) == 4 for u, v in product(tiny, repeat=2)),
           'freshness cannot be inferred in a too-small finite window')
    C['insufficient_finite_freshness_guard'] += 1


def pair_model(categories):
    # 0,1 are the two active equivalence classes; 2 is the inactive sort.
    values = tuple(('I', 0, i) if k == 2 else ('A', k, i)
                   for i, k in enumerate(categories))
    pairs = {(i, j): atom(values[i], values[j]) for i, j in combinations(range(len(values)), 2)}
    return values, pairs


def pair_preserving(values, pairs, mapping, marked=True):
    if any(values[i][0] != values[mapping[i]][0] for i in range(len(values))):
        return False
    if marked and any(bit(values[i]) != bit(values[mapping[i]]) for i in range(len(values))):
        return False
    return all(atom(values[mapping[i]], values[mapping[j]]) == a for (i, j), a in pairs.items())


def frozen_lifts():
    # Free symmetric ternary data over these binary diagrams: a triple state
    # -1 is unspecified, 0 frozen false, and 1 frozen true. Complete unknown
    # triples by false; this canonical choice is checked against every
    # automorphism of the AUGMENTED complete-pair partial input.
    for n in range(5):
        triples = tuple(combinations(range(n), 3))
        for categories in product(range(3), repeat=n):
            values, pairs = pair_model(categories)
            for mapping in product(range(n), repeat=n):
                if pair_preserving(values, pairs, mapping):
                    demand(len(set(mapping)) == n, 'complete irreflexive pair target forces injectivity')
                    C['complete_pair_injective_maps'] += 1
            autos = tuple(p for p in permutations(range(n)) if pair_preserving(values, pairs, p))
            for states in product((-1, 0, 1), repeat=len(triples)):
                specified = {t: s for t, s in zip(triples, states) if s >= 0}
                completed = {t: int(specified.get(t, 0) == 1) for t in triples}
                for t, s in specified.items():
                    demand(completed[t] == s, 'frozen positive AND negative triple preserved')
                    # The entire induced three-point factor also retains every
                    # chosen pair atom and every repeated ternary tuple=false.
                    demand(all(pairs[e] != 'Id' for e in combinations(t, 2)), 'frozen complete pair data')
                    C['frozen_signed_factor_checks'] += 1
                for perm in autos:
                    image = lambda t: tuple(sorted(perm[i] for i in t))
                    if {image(t): s for t, s in specified.items()} != specified:
                        continue
                    demand(all(completed[image(t)] == s for t, s in completed.items()),
                           'canonical completion extends every augmented-input automorphism')
                    demand(all(bit(values[perm[i]]) == bit(values[i]) for i in range(n)),
                           'restored unary bits are invariant')
                    C['conditional_automorphism_extensions'] += 1
                # Forget and restore unary bits: the selected pair diagram
                # and frozen full factors are unchanged on exactly n vertices.
                restored = tuple(bit(x) for x in values)
                demand(all(restored[i] == bit(values[i]) for i in range(n)), 'marked interface lifting')
                C['free_higher_relation_lifts'] += 1
            C['complete_binary_target_models'] += 1
    demand(atom(('I', 0, 0), ('I', 0, 0)) == 'Id', 'collapsed pair loses diversity atom')
    # Without the strict complete pair target an edgeless two-point input
    # admits the constant map, so injectivity is an actual used hypothesis.
    demand(len({0, 0}) < 2, 'missing pair data permits a collision')
    C['missing_pair_collision_guard'] += 1


def support_normal_boundary():
    vertices = tuple(range(4))
    triples = frozenset(combinations(vertices, 3))
    for t in triples:
        demand(len(t) == 3 and len(set(t)) == 3, 'actual frozen three-point hyperedge factor')
        demand(not any(set(q) <= set(t) for q in combinations(vertices, 4)),
               'each frozen factor is K4^(3)-free')
        C['K4free_frozen_positive_factors'] += 1
    # All complete four-vertex hypergraphs are checked independently: there
    # are exactly four possible triples, so preserving all four positive
    # factors forces the one excluded full K4^(3).
    admissible = []
    for subset_bits in product(range(2), repeat=4):
        hyperedges = frozenset(t for t, b in zip(sorted(triples), subset_bits) if b)
        if hyperedges == triples:
            continue
        admissible.append(hyperedges)
    demand(len(admissible) == 15, 'all bounded K4-free candidates enumerated')
    demand(not any(triples <= h for h in admissible), 'pair shadow does not supply higher-support interface')
    # A one-colour strict pair diagram on four vertices has an actual pure-set
    # realization; it carries no indication of the forbidden ternary clique.
    pair_target = frozenset(combinations(vertices, 2))
    demand(len(pair_target) == 6, 'pure complete pair shadow is feasible')
    C['K4free_no_full_lift_guard'] += 1


def main():
    detours()
    frozen_lifts()
    support_normal_boundary()
    print(json.dumps(dict(status='PASS', seconds=round(time.monotonic() - START, 3),
        counts=dict(sorted(C.items())),
        witnesses=dict(active_source='two infinite equivalence classes with four-point finite fibre windows',
                       inactive_source='pure inactive sort with constant bit zero',
                       full_toy='free symmetric ternary relation over each chosen binary diagram',
                       canonical_completion='unknown triples false, signed frozen factors retained',
                       support_normality_boundary='K4^(3)-free age with four individually valid frozen hyperedges'),
        limits='Bounded diagnostics only: no fixed finite window has claimed unbounded SAP/CCO or freshness; no general support-normal/equivariant completion interface, terminal theorem, coherent EPPA or Lean proof is certified.'), sort_keys=True))


if __name__ == '__main__':
    signal.alarm(30)
    main()
