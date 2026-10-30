#!/usr/bin/env python3
"""Bounded B044 diagnostics for phase supports and real equality folding.

The active window consists of four two-point equivalence classes, with
mate and different-class binary atoms. Its oriented-pair character has
rigid identity/mate sheets and a nonrigid, phase-flexible atom. A separate
inactive singleton sort checks that inactive endpoints do not introduce
independent phase bits. The finite window is an oracle for the bounded
instances here, NOT a claim that this finite restriction has general CCO.
All relation products and cycle/path witnesses are actual finite-set
computations. The completion routine is checked against independent
finite homomorphism search. No general AP/CCO theorem, source gate,
infinite Fraisse construction or Lean proof is certified.
Reproduce: timeout 20s python tools/check_ap_character_controls.py
"""
from collections import Counter
from itertools import combinations, product
import json
import signal
import time

START = time.monotonic()


def require(ok, message, witness=None):
    if not ok:
        raise AssertionError((message, witness))


def tick():
    require(time.monotonic() - START < 30, '30-second diagnostic deadline')


def compose(r, s):
    targets = {}
    for y, z in s:
        targets.setdefault(y, set()).add(z)
    return frozenset((x, z) for x, y in r for z in targets.get(y, ()))


def source():
    active = tuple((i, b) for i in range(4) for b in range(2))
    inactive = (('inactive', 0),)
    carriers = {'a': active, 'i': inactive}
    atoms = {}
    for s, t in product(carriers, repeat=2):
        typed = {}
        for x, y in product(carriers[s], carriers[t]):
            if s == t == 'a':
                label = 'Id' if x == y else 'mate' if x[0] == y[0] else 'far'
            elif s == t:
                label = 'Id'
            else:
                label = 'cross'
            typed.setdefault(label, set()).add((x, y))
        atoms[s, t] = {k: frozenset(v) for k, v in typed.items()}
    return carriers, atoms


def algebra_controls(counts, witnesses):
    carriers, atoms = source()
    tables = {}
    for s, t, u in product(carriers, repeat=3):
        for a, b in product(atoms[s, t], atoms[t, u]):
            relation = compose(atoms[s, t][a], atoms[t, u][b])
            support = frozenset(c for c, r in atoms[s, u].items() if r & relation)
            require(relation == frozenset().union(*(atoms[s, u][c] for c in support)), 'products are unions of whole actual atoms')
            require(support, 'nonempty typed factors have nonempty product')
            tables[s, t, u, a, b] = support
            counts['actual_typed_products'] += 1

    def mul(s, t, u, left, right):
        return frozenset().union(*(tables[s, t, u, a, b] for a, b in product(left, right)))

    def mask(s, t, e, f):
        if s != 'a' or t != 'a':
            return frozenset(atoms[s, t])
        return frozenset(('Id', 'far') if e == f else ('mate', 'far'))

    profiles = {key: {frozenset((a,)) for a in palette} for key, palette in atoms.items()}
    # Actual word profiles, including logical identities as output atoms.
    for length in range(1, 5):
        for sorts in product(carriers, repeat=length + 1):
            for word in product(*(atoms[sorts[j], sorts[j+1]] for j in range(length))):
                old = frozenset((word[0],))
                for j in range(1, length):
                    old = mul(sorts[0], sorts[j], sorts[j+1], old, frozenset((word[j],)))
                profiles[sorts[0], sorts[-1]].add(old)
                for bits in product(*((0, 1) if s == 'a' else (0,) for s in sorts)):
                    if any(word[j] not in mask(sorts[j], sorts[j+1], bits[j], bits[j+1]) for j in range(length)):
                        continue
                    lifted = frozenset((word[0],))
                    prefix = lifted
                    for j in range(1, length):
                        prefix = mul(sorts[0], sorts[j], sorts[j+1], prefix, frozenset((word[j],)))
                        lifted = mul(sorts[0], sorts[j], sorts[j+1], lifted, frozenset((word[j],))) & mask(sorts[0], sorts[j+1], bits[0], bits[j+1])
                        require(lifted == prefix & mask(sorts[0], sorts[j+1], bits[0], bits[j+1]), 'path normal form', (sorts, word, bits))
                        require(lifted, 'nonempty lifted path')
                    counts['typed_marked_words'] += 1
        tick()
    for s, t, u in product(carriers, repeat=3):
        for e, f, g in product(*((0, 1) if x == 'a' else (0,) for x in (s, t, u))):
            for a, b in product(mask(s, t, e, f), mask(t, u, f, g)):
                require(tables[s, t, u, a, b] & mask(s, u, e, g), 'fork totality')
                counts['fork_totality_checks'] += 1
    for (s, t), words in profiles.items():
        words = tuple(words)
        for size in range(1, len(words) + 1):
            for family in combinations(words, size):
                intersection = frozenset.intersection(*family)
                if not intersection:
                    continue
                for e, f in product(*((0, 1) if x == 'a' else (0,) for x in (s, t))):
                    allowed = mask(s, t, e, f)
                    if all(p & allowed for p in family):
                        require(intersection & allowed, 'phase primality for actual word profiles')
                        counts['phase_primality_checks'] += 1
    witnesses['inactive_bit_boundary'] = {'inactive_available_bits': [0], 'cross_mask_is_entire_palette': True}
    witnesses['logical_identity_output'] = {'mate_times_mate': sorted(tables['a', 'a', 'a', 'mate', 'mate']), 'identity_is_not_a_specified_diversity_edge': True}
    return carriers, atoms, tables


def edges_lookup(edges, x, y):
    return edges.get(tuple(sorted((x, y))))


def paths(vertices, edges, x, y):
    def walk(v, path):
        if v == y:
            yield tuple(path)
            return
        for w in vertices:
            if w not in path and edges_lookup(edges, v, w) is not None:
                yield from walk(w, path + [w])
    yield from walk(x, [x])


def cycles(vertices, edges):
    for start in vertices:
        def walk(v, path):
            for w in vertices:
                if edges_lookup(edges, v, w) is None:
                    continue
                if w == start and len(path) >= 3 and path[1] < path[-1]:
                    yield tuple(path)
                elif w > start and w not in path:
                    yield from walk(w, path + [w])
        yield from walk(start, [start])


def hom(vertices, edges, bits=None):
    """Independent search into the actual oriented-pair window."""
    image = {}
    order = sorted(vertices, key=lambda x: -sum(x in edge for edge in edges))
    candidates = tuple(product(range(4), range(2)))
    def search(k):
        if k == len(order):
            return dict(image)
        v = order[k]
        for value in candidates:
            if bits is not None and value[1] != bits[v]:
                continue
            good = True
            for w, target in image.items():
                label = edges_lookup(edges, v, w)
                if label == 'mate' and not (value[0] == target[0] and value[1] != target[1]):
                    good = False
                if label == 'far' and value[0] == target[0]:
                    good = False
            if good:
                image[v] = value
                result = search(k + 1)
                if result is not None:
                    return result
                del image[v]
        return None
    return search(0)


def graph_controls(counts, witnesses, tables):
    palette = frozenset(('Id', 'mate', 'far'))
    def profile(path, edges):
        result = frozenset(('Id',))
        for x, y in zip(path, path[1:]):
            label = edges_lookup(edges, x, y)
            result = frozenset().union(*(tables['a', 'a', 'a', a, label] for a in result))
        return result
    def old_cycles_ok(vertices, edges):
        return all('Id' in profile(c + (c[0],), edges) for c in cycles(vertices, edges))
    def complete(vertices0, edges0, bits0):
        vertices, edges, bits = list(vertices0), dict(edges0), dict(bits0)
        quotient = {v: v for v in vertices}
        while len(edges) < len(vertices) * (len(vertices) - 1) // 2:
            before = len(vertices), len(vertices) * (len(vertices) - 1) // 2 - len(edges)
            x, y = next(p for p in combinations(vertices, 2) if p not in edges)
            individual = tuple(profile(p, edges) for p in paths(vertices, edges, x, y))
            common = frozenset.intersection(*individual) if individual else palette
            allowed = frozenset(('Id', 'far') if bits[x] == bits[y] else ('mate', 'far'))
            choices = common & allowed
            require(choices, 'completion has allowed common output', (vertices, edges, bits, x, y))
            c = next(a for a in ('Id', 'mate', 'far') if a in choices)
            if c != 'Id':
                edges[x, y] = c
                counts['diversity_insertions'] += 1
            else:
                require(all('Id' in p for p in individual), 'fold identity lies in every simple path profile')
                require(bits[x] == bits[y], 'fold preserves actual endpoint bits')
                new_edges = {}
                for (v, w), label in edges.items():
                    v, w = x if v == y else v, x if w == y else w
                    require(v != w, 'fold never identifies adjacent vertices')
                    pair = tuple(sorted((v, w)))
                    require(pair not in new_edges or new_edges[pair] == label, 'duplicate incident labels agree')
                    new_edges[pair] = label
                edges = new_edges
                vertices.remove(y)
                for v in quotient:
                    if quotient[v] == y:
                        quotient[v] = x
                del bits[y]
                counts['actual_identity_contractions'] += 1
            require(old_cycles_ok(vertices, edges), 'all quotient/new-edge cycles remain old-feasible')
            after = len(vertices), len(vertices) * (len(vertices) - 1) // 2 - len(edges)
            require(after < before, 'lexicographic termination')
        result = hom(vertices, edges, bits)
        require(result is not None, 'complete old diagram has actual marked realization')
        composed = {v: result[quotient[v]] for v in quotient}
        require(all(composed[v][1] == bits0[v] for v in vertices0), 'all original bits retained')
        for (v, w), label in edges0.items():
            require(composed[v] != composed[w], 'original diversity edges retained')
            require((composed[v][0] == composed[w][0]) == (label == 'mate'), 'old atomic labels retained')
        return composed

    for n in range(5):
        vertices = tuple(range(n))
        pairs = tuple(combinations(vertices, 2))
        for labels in product((None, 'mate', 'far'), repeat=len(pairs)):
            edges = {p: a for p, a in zip(pairs, labels) if a is not None}
            feasible = old_cycles_ok(vertices, edges)
            require((hom(vertices, edges) is not None) == feasible, 'bounded old cycle criterion vs independent hom search')
            counts['old_partial_graphs'] += 1
            if not feasible:
                continue
            for assignment in product((0, 1), repeat=n):
                bits = dict(zip(vertices, assignment))
                if any(a == 'mate' and bits[x] == bits[y] for (x, y), a in edges.items()):
                    continue
                require(hom(vertices, edges, bits) is not None, 'independent marked completion exists')
                complete(vertices, edges, bits)
                counts['marked_completions'] += 1
            tick()
    # Ordinary AP may be forced to identify mates of a shared point.
    vertices = (0, 1, 2)
    edges = {(0, 1): 'mate', (0, 2): 'mate'}
    image = complete(vertices, edges, {0: 0, 1: 1, 2: 1})
    require(image[1] == image[2], 'AP-only witness forces cross-leg equality')
    require(image[0] != image[1], 'each complete leg remains injective')
    witnesses['AP_not_SAP_pairing_span'] = {'base': [0], 'left_leg': [0, 1], 'right_leg': [0, 2], 'forced_cross_leg_collision': [1, 2], 'each_leg_injective': True}
    # Explicit cycle born by folding, absent from the old graph.
    edges = {(0, 1): 'mate', (1, 2): 'far', (2, 3): 'far'}
    require(not tuple(cycles((0, 1, 2, 3), edges)), 'pre-fold graph is a path')
    require('Id' in profile((0, 1, 2, 3), edges), 'path can close by actual identity')
    folded = {(0, 1): 'mate', (1, 2): 'far', (0, 2): 'far'}
    require(old_cycles_ok((0, 1, 2), folded), 'new quotient triangle has an actual old homomorphism')
    witnesses['fold_created_cycle'] = {'old_path': ['mate', 'far', 'far'], 'new_cycle': ['mate', 'far', 'far'], 'actual_identity_endpoint_witness': True}


def rank_controls(counts, witnesses):
    for length in range(1, 5):
        for ranks in product(range(1, 6), repeat=length):
            before = sum(3**k for k in ranks)
            for active_bits in product((0, 1), repeat=length):
                if not any(active_bits):
                    continue
                after = sum(2 * 3**(k-1) if a else 3**k for k, a in zip(ranks, active_bits))
                require(after < before, 'strict integer potential drop')
                counts['rank_drop_checks'] += 1
    witnesses['rank_zero_guard'] = 'An active parent must contain a realized phase-one diversity atom, hence k>=1.'


def main():
    counts, witnesses = Counter(), {}
    _, _, tables = algebra_controls(counts, witnesses)
    graph_controls(counts, witnesses, tables)
    rank_controls(counts, witnesses)
    print(json.dumps(dict(status='PASS', seconds=round(time.monotonic()-START, 3), counts=dict(sorted(counts.items())), witnesses=witnesses,
        limits='Bounded actual finite-set diagnostics, not a general CCO/AP/SAP, source maximal-gate, affine-slice, Fraisse or Lean proof; the finite paired window itself is not claimed to satisfy unbounded CCO.'), sort_keys=True))


if __name__ == '__main__':
    signal.alarm(30)
    main()
