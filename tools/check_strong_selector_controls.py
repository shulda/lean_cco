#!/usr/bin/env python3
"""Finite palette controls for the STRONG sidecar; not Lean proofs.

The ultrametric table is interpreted as a palette, not a finite structure
claimed to have SAP. R05 exhausts four-vertex partial graphs only.
"""
from itertools import combinations, permutations, product


def require(condition, message):
    if not condition:
        raise AssertionError(message)


def intersection(family, top):
    return frozenset.intersection(top, *family)


def subsets(items):
    for n in range(len(items) + 1):
        yield from combinations(items, n)


def set_product(a, b, atomic):
    return frozenset(c for x in a for y in b for c in atomic(x, y))


def pc(a, b, c, multiply):
    # The controls use literal self-converse colours on all tagged palettes.
    return c <= multiply(a, b) and a <= multiply(c, b) and b <= multiply(a, c)


def check():
    # R01: represented F2^2 atom products versus distinct-triangle products.
    def thin(a, b):
        return frozenset({a ^ b}) if a != b else frozenset()

    require(not thin(1, 1), 'R01: repeated thin atom has no distinct triangle')
    left = set_product(thin(1, 1), frozenset({2}), thin)
    right = set_product(frozenset({1}), thin(1, 2), thin)
    require(left != right and right == {2}, 'R01: associativity really needs SAP')
    word = (1, 1, 2)
    walk = [0]
    for atom in word:
        walk.append(walk[-1] ^ atom)
    require(walk[-1] == 2 and len(set(walk)) < 4, 'R01: guarded represented survivor')
    require(not any(all(p[i] ^ p[i+1] == word[i] for i in range(3))
                    for p in permutations(range(4))), 'R01: no injective word realization')

    # R02: three-level ultrametric triangle palette, two named sorts.
    top = frozenset({1, 2, 3})

    def ultra(a, b):
        return frozenset(range(1, a + 1)) if a == b else frozenset({max(a, b)})

    multiply = lambda a, b: set_product(a, b, ultra)
    profiles = {frozenset({a}) for a in top}
    while True:
        extended = profiles | {multiply(a, b) for a, b in product(profiles, repeat=2)}
        if extended == profiles:
            break
        profiles = extended
    exact = {intersection(family, top) for family in subsets(list(profiles))}
    exact.discard(frozenset())
    require(len(exact) == 5, 'R02: expected nontrivial nested exact system')
    for a, b, c in product(exact, repeat=3):
        require(multiply(multiply(a, b), c) == multiply(a, multiply(b, c)), 'R02: associativity')
    for family in subsets(list(exact)):
        meet = intersection(family, top)
        if all(a & b for a, b in combinations(family, 2)):
            require(bool(meet), 'R02: exact Helly')
        if meet:
            for a in exact:
                require(multiply(a, meet) == intersection([multiply(a, b) for b in family], top),
                        'R02: nonempty-result distribution')
    tagged = {(i, j, a) for i, j in product(range(2), repeat=2) for a in exact}

    def converse(node):
        i, j, a = node
        return j, i, a

    def swap(node):
        i, j, a = node
        return 1-i, 1-j, a

    def generated(seed):
        family = {seed}
        while True:
            new = family | {converse(x) for x in family} | {swap(x) for x in family}
            for i, j, a in family:
                for k in range(2):
                    for b in exact:
                        new.add((k, j, multiply(b, a)))
                        new.add((i, k, multiply(a, b)))
            if new == family:
                return frozenset(family)
            family = new

    generated_families = {seed: generated(seed) for seed in tagged}
    for a, b in product(tagged, repeat=2):
        if a[:2] == b[:2] and generated_families[a] == generated_families[b]:
            require(a == b, 'R02: parallel pure-tag no-return')

    def check_pruning(domain, mapping):
        for node in domain:
            i, j, a = node
            out = mapping[node]
            require(out[:2] == (i, j) and bool(out[2]) and out[2] <= a and out[2] in exact,
                    'R02: nonempty original exact output')
            require(mapping[converse(node)] == converse(out), 'R02: converse')
            require(mapping[swap(node)] == swap(out), 'R02: pure tag covariance')
            for smaller in domain:
                if smaller[:2] == (i, j) and smaller[2] <= a and smaller[2] & out[2]:
                    require(mapping[smaller][2] == smaller[2] & out[2], 'R02: survivor heredity')
        for i, j, k in product(range(2), repeat=3):
            aa = [x for x in domain if x[:2] == (i, j)]
            bb = [x for x in domain if x[:2] == (j, k)]
            cc = [x for x in domain if x[:2] == (i, k)]
            for a, b, c in product(aa, bb, cc):
                if pc(a[2], b[2], c[2], multiply):
                    require(pc(mapping[a][2], mapping[b][2], mapping[c][2], multiply),
                            'R02: ALL PC coordinates survive')

    current = set(tagged)
    composite = {x: x for x in tagged}
    gate_count = 0
    while any(len(x[2]) > 1 for x in current):
        viable = [seed for seed in tagged if any(seed[:2] == d[:2] and
                  bool(seed[2] & d[2]) and seed[2] & d[2] != d[2] for d in current)]
        seed = min(viable, key=lambda x: (len(generated_families[x]), x[0], x[1], sorted(x[2])))
        family = generated_families[seed]
        mapping = {}
        for d in current:
            active = [a[2] for a in family if a[:2] == d[:2] and a[2] & d[2]]
            require(all(a & b for a, b in combinations(active, 2)), 'R02: visibility')
            mapping[d] = (*d[:2], intersection([d[2], *active], top))
        check_pruning(current, mapping)
        image = set(mapping.values())
        require(image < current, 'R02: strict descent in NUMBER of current menus')
        require(all(mapping[x] == x for x in image), 'R02: image equals fixed family')
        require(all(e in image for d in image for e in tagged
                    if e[:2] == d[:2] and e[2] <= d[2]), 'R02: downward image')
        composite = {x: mapping[y] for x, y in composite.items()}
        current = image
        gate_count += 1
    require(gate_count <= len(tagged)-12 and len(current) == 12, 'R02: singleton-count bound')
    check_pruning(tagged, composite)
    require(all(len(x[2]) == 1 for x in composite.values()), 'R02: final HS')
    require(multiply(frozenset({1}), frozenset({1})) == {1} != top,
            'R02: stable loop power need not be Top')

    # R03: infinite two-block equivalence palette; triangle parity is even.
    parity = lambda a, b: frozenset({a ^ b})
    parity_product = lambda a, b: set_product(a, b, parity)
    parity_top = frozenset({0, 1})
    cross = frozenset({1})
    require(pc(parity_top, parity_top, cross, parity_product), 'R03: input PC triple')
    require(all(not pc(frozenset({choice}), frozenset({choice}), cross, parity_product)
                for choice in parity_top), 'R03: no PC-preserving selector on Top')
    power = cross
    powers = []
    for _ in range(6):
        powers.append(power)
        power = parity_product(power, cross)
    require(all(powers[i] != powers[i+1] for i in range(5)), 'R03: loop powers alternate')

    # R04: a literal two-colour transposition fixes Top but fixes no atom.
    require(not any(choice == 1-choice for choice in [0, 1]),
            'R04: arbitrary colour covariance cannot replace a pure tag action')

    # R05: all 4^6 partial graphs on four distinct vertices.
    vertices = range(4)
    pairs = list(combinations(vertices, 2))
    legal_completions = []
    for colours in product(top, repeat=len(pairs)):
        completion = dict(zip(pairs, colours))
        if all([completion[i, j], completion[i, k], completion[j, k]].count(
               max(completion[i, j], completion[i, k], completion[j, k])) >= 2
               for i, j, k in combinations(vertices, 3)):
            legal_completions.append(completion)
    checked = 0
    for values in product(range(4), repeat=len(pairs)):
        specified = {pair: v for pair, v in zip(pairs, values) if v}
        domains = {(i, j): frozenset({specified[tuple(sorted((i, j)))]})
                   if tuple(sorted((i, j))) in specified else top
                   for i, j in permutations(vertices, 2)}
        while True:
            updated = {(i, j): d & intersection([multiply(domains[i, k], domains[k, j])
                        for k in vertices if k not in (i, j)], top)
                       for (i, j), d in domains.items()}
            if updated == domains:
                break
            domains = updated
        completions = [c for c in legal_completions if all(c[p] == v for p, v in specified.items())]
        if not completions:
            require(any(not d for d in domains.values()), 'R05: detect inconsistent diagram')
            continue
        for i, j in permutations(vertices, 2):
            pair = tuple(sorted((i, j)))
            actual = frozenset(c[pair] for c in completions)
            require(domains[i, j] == actual, 'R05: PC equals exact completion survivors')
            paths = []
            others = [k for k in vertices if k not in (i, j)]
            for length in range(len(others)+1):
                for internal in permutations(others, length):
                    path = (i, *internal, j)
                    edges = [tuple(sorted((x, y))) for x, y in zip(path, path[1:])]
                    if all(e in specified for e in edges):
                        profile = frozenset({specified[edges[0]]})
                        for edge in edges[1:]:
                            profile = multiply(profile, frozenset({specified[edge]}))
                        paths.append(profile)
            require(domains[i, j] == intersection(paths, top), 'R05: simple-path formula')
        checked += 1
    return f'R01–R05 passed; {gate_count} pure-tag gates and {checked}/4096 completable four-vertex diagrams. No general proof claimed.'


if __name__ == '__main__':
    print(check())
