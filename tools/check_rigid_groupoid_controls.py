#!/usr/bin/env python3
"""Finite represented controls for rigid groupoids and affine translate Helly.

Relations, saturation and bijections below are literal finite relations.  A
supplied subgroup family only tests conjugation and dominance as relation
laws; RAW word-exactness is not computed. Neither invariant nor projected
gates are silently declared word-exact. No CCO/AP/SAP certification is claimed.
"""
from functools import lru_cache
from itertools import combinations, product


def require(value, message):
    if not value:
        raise AssertionError(message)


def bits(mask):
    while mask:
        bit = mask & -mask
        yield bit.bit_length() - 1
        mask -= bit


@lru_cache(maxsize=8192)
def compose(a, b):
    result = []
    for row in a:
        value = 0
        for middle in bits(row):
            value |= b[middle]
        result.append(value)
    return tuple(result)


@lru_cache(maxsize=1024)
def converse(a):
    result = [0] * len(a)
    for x, row in enumerate(a):
        for y in bits(row):
            result[y] |= 1 << x
    return tuple(result)


def union(relations, n):
    result = [0] * n
    for relation in relations:
        for i, row in enumerate(relation):
            result[i] |= row
    return tuple(result)


def contained(a, b):
    return all(x & ~y == 0 for x, y in zip(a, b))


def subgroups(d):
    return [s for s in range(1, 1 << (1 << d), 2)
            if all(s >> (a ^ b) & 1 for a in bits(s) for b in bits(s))]


class Model:
    def __init__(self, d, orbits=2):
        self.d, self.g, self.orbits = d, 1 << d, orbits
        # Extra real fibre has two points: object identity K is not logical Id.
        self.points = tuple(product(range(orbits), range(self.g), range(2)))
        self.index = {x: i for i, x in enumerate(self.points)}
        self.n = len(self.points)
        self.identity = tuple(1 << i for i in range(self.n))
        self.gate = self.relation(0, 0, 0)
        self.arrows = {(a, b, g): self.relation(a, b, g)
                       for a, b, g in product(range(3), range(3), range(self.g))}

    def rotate(self, value, count):
        count %= self.d
        mask = self.g - 1
        return ((value << count) | (value >> ((self.d - count) % self.d))) & mask

    def chart(self, obj, value):
        return self.rotate(value, obj) ^ ((3 * obj) % self.g)

    def unchart(self, obj, value):
        return self.rotate(value ^ ((3 * obj) % self.g), -obj)

    def relation(self, a, b, shift, fine=None):
        rows = []
        for orbit, phase, fibre in self.points:
            target_phase = self.unchart(b, self.chart(a, phase) ^ shift)
            targets = range(2) if fine is None else [fibre ^ fine]
            rows.append(sum(1 << self.index[orbit, target_phase, t] for t in targets))
        return tuple(rows)

    @lru_cache(maxsize=None)
    def equivalence(self, obj, subgroup):
        return union((self.relation(obj, obj, h) for h in bits(subgroup)), self.n)

    def menus(self, a, b):
        atoms = [self.relation(a, b, h, fine=f) for h, f in product(range(self.g), range(2))]
        cross = tuple(sum(1 << j for j, y in enumerate(self.points) if x[0] != y[0])
                      for x in self.points)
        atoms.append(cross)
        return [union((atoms[i] for i in bits(mask)), self.n) for mask in range(1 << len(atoms))]


def groupoid_controls():
    arrows = products = families = 0
    for d in range(1, 4):
        model = Model(d)
        k = model.gate
        require(k != model.identity and compose(k, k) == k, 'object gate differs from logical real identity')
        for (a, b, g), r in model.arrows.items():
            require(compose(r, converse(r)) == compose(converse(r), r) == k,
                    'actual bridge source and unique target kernels')
            require(compose(k, r) == compose(r, k) == r, 'actual bridge bisaturation')
            for h in range(model.g):
                s = model.arrows[a, b, h]
                require(g == h or all(not (x & y) for x, y in zip(r, s)), 'rigid arrows never agree at a quotient point')
                require(compose(model.arrows[a, a, g ^ h], s) == r,
                        'each hom-set is an actual endpoint torsor')
            arrows += 1
        for a, b, c, g, h in product(range(3), range(3), range(3), range(model.g), range(model.g)):
            require(compose(model.arrows[a, b, g], model.arrows[b, c, h]) == model.arrows[a, c, g ^ h],
                    'actual bridge composition follows elementary-abelian group law')
            products += 1
        groups = subgroups(d)
        for t in range(1, model.g):
            eligible = [h for h in groups if h != 1 and h >> t & 1]
            # All menus containing the trivial and whole subgroup and satisfying
            # dominance; retain those closed under meet and subgroup join.
            whole = (1 << model.g) - 1
            optional = [h for h in eligible if h != whole]
            for mask in range(1 << len(optional)):
                family = {1, whole} | {optional[i] for i in bits(mask)}
                def subgroup_join(a, b):
                    return sum(1 << x for x in {u ^ v for u in bits(a) for v in bits(b)})
                if any((a & b) not in family or subgroup_join(a, b) not in family
                       for a, b in product(family, repeat=2)):
                    continue
                families += 1
                for b in range(3):
                    transported = []
                    for g in range(model.g):
                        r = model.arrows[0, b, g]
                        tb = compose(compose(converse(r), model.arrows[0, 0, t]), r)
                        transported.append(tb)
                        require(tb != k and compose(tb, tb) == k, 'transported dominant involution is nonidentity')
                        for h in family:
                            za, zb = model.equivalence(0, h), model.equivalence(b, h)
                            require(compose(compose(r, zb), converse(r)) == za
                                    and compose(compose(converse(r), za), r) == zb,
                                    'actual conjugation and inverse on the supplied subgroup family')
                            if h != 1:
                                require(contained(tb, zb), 'dominance survives every bridge path')
                    require(len(set(transported)) == 1, 'transported involution is independent of bridge path')
    return arrows, products, families


def rigid_factor_controls():
    model = Model(1)
    left, right = model.menus(0, 1)[1:], model.menus(1, 2)[1:]
    count = 0
    for a, b in product(left, right):
        ab = compose(a, b)
        for g in range(model.g):
            r = model.arrows[0, 2, g]
            if not contained(ab, r):
                continue
            require(all(a) and all(b) and all(converse(a)) and all(converse(b)),
                    'arbitrary invariant menu relations are serial and surjective')
            r1 = compose(model.gate, a)
            kb = compose(converse(r1), r1)
            r2 = compose(converse(r1), r)
            require(contained(a, r1) and contained(b, r2) and compose(r1, r2) == r,
                    'actual rigid-product factorization for AB contained in R')
            require(compose(r1, converse(r1)) == model.gate and kb == model.gate
                    and compose(r2, converse(r2)) == kb and compose(converse(r2), r2) == model.gate,
                    'constructed factors satisfy actual bridge equations')
            count += 1
    require(count > 0 and any(a != compose(model.gate, a) for a in left),
            'factor menu includes genuine unsaturated proper subrelations')
    return len(left), count


def quotient_controls():
    saturated_count = bridge_count = composition_count = 0
    for d in [1, 2]:
        model = Model(d)
        qpoints = tuple(product(range(model.orbits), range(model.g)))
        qindex = {q: i for i, q in enumerate(qpoints)}
        qid = tuple(1 << i for i in range(len(qpoints)))
        def project(r):
            rows = [0] * len(qpoints)
            for x, row in enumerate(r):
                for y in bits(row):
                    rows[qindex[model.points[x][:2]]] |= 1 << qindex[model.points[y][:2]]
            return tuple(rows)
        def pullback(r):
            return tuple(sum(1 << j for j, y in enumerate(model.points)
                             if r[qindex[x[:2]]] >> qindex[y[:2]] & 1) for x in model.points)
        # Objects 0,1,2 use different actual coordinate charts.
        menus = {(a, b): model.menus(a, b) for a, b in [(0, 1), (1, 2), (0, 2)]}
        saturated = {key: [r for r in values if compose(compose(model.gate, r), model.gate) == r]
                     for key, values in menus.items()}
        for r in saturated[0, 1]:
            qr = project(r)
            require(pullback(qr) == r and project(converse(r)) == converse(qr),
                    'actual bisaturation quotient/pullback bijection and converse')
            old_bridge = compose(r, converse(r)) == compose(converse(r), r) == model.gate
            new_bridge = compose(qr, converse(qr)) == compose(converse(qr), qr) == qid
            require(old_bridge == new_bridge, 'actual functional bridges correspond across quotient')
            saturated_count += 1
            bridge_count += int(old_bridge)
        require(len({project(r) for r in saturated[0, 1]}) == len(saturated[0, 1]), 'quotient map is injective on saturated relations')
        for a, b in product(saturated[0, 1], saturated[1, 2]):
            require(project(compose(a, b)) == compose(project(a), project(b)),
                    'actual saturated quotient composition formula')
            composition_count += 1
    return saturated_count, bridge_count, composition_count


def phase_controls():
    # Enumerate every bit assignment on the entire finite quotient universe.
    model = Model(1)
    points = tuple(product(range(3), range(model.orbits), range(model.g)))
    n = len(points)
    gauge = [0, 1, 0]
    def character(a, b, shift):
        return shift ^ gauge[a] ^ gauge[b]
    global_seeds = []
    for seed in product(range(2), repeat=model.orbits):
        global_seeds.append(tuple(seed[o] ^ model.chart(a, x) ^ gauge[a] for a, o, x in points))
    edges = [(i, j, character(a, b, model.chart(a, x) ^ model.chart(b, y)))
             for i, (a, o, x) in enumerate(points) for j, (b, p, y) in enumerate(points) if o == p]
    actual = []
    for assignment in product(range(2), repeat=n):
        if all(assignment[i] ^ assignment[j] == gain for i, j, gain in edges):
            actual.append(assignment)
    require(set(actual) == set(global_seeds), 'all global bit markings equal independent orbit-seed markings')
    partial = inconsistent = 0
    for chosen in combinations(range(n), 3):
        for prescribed in product(range(2), repeat=3):
            extendible = any(all(marking[i] == bit for i, bit in zip(chosen, prescribed)) for marking in actual)
            pairwise = True
            for (i, u), (j, v) in combinations(zip(chosen, prescribed), 2):
                a, o, x = points[i]
                b, p, y = points[j]
                if o == p:
                    pairwise &= u ^ v == character(a, b, model.chart(a, x) ^ model.chart(b, y))
            require(extendible == pairwise, 'finite prescribed phases: actual extension iff pairwise seed test')
            inconsistent += int(not extendible)
            partial += 1
    for i, (a, o, x) in enumerate(points):
        for j, (b, p, y) in enumerate(points):
            differences = {marking[i] ^ marking[j] for marking in actual}
            require(differences == ({character(a, b, model.chart(a, x) ^ model.chart(b, y))} if o == p else {0, 1}),
                    'rigid pair forced phase; nonrigid pair admits both phases')
    require(inconsistent > 0, 'inconsistent triples are actually covered')
    return 1 << n, len(actual), partial, inconsistent


def affine_translate_controls():
    sets = affine = families = 0
    for d in range(1, 4):
        g = 1 << d
        for subset in range(1, 1 << g):
            translates = sorted({sum(1 << (x ^ shift) for x in bits(subset)) for shift in range(g)})
            helly = True
            for chosen in range(1, 1 << len(translates)):
                selected = [translates[i] for i in bits(chosen)]
                if not all(a & b for a, b in combinations(selected, 2)):
                    continue
                intersection = (1 << g) - 1
                for value in selected:
                    intersection &= value
                families += 1
                if not intersection:
                    helly = False
                    break
            origin = next(bits(subset))
            shifted = {x ^ origin for x in bits(subset)}
            coset = all(a ^ b in shifted for a, b in product(shifted, repeat=2))
            require(helly == coset, 'actual pairwise-intersecting translate Helly iff affine coset')
            sets += 1
            affine += int(coset)
    require(sets == 273 and affine == 65, 'all nonempty subsets of F2^d for d=1,2,3')
    return sets, affine, families


def run_controls():
    arrows, products, families = groupoid_controls()
    menus, factors = rigid_factor_controls()
    saturated, bridges, quotient_products = quotient_controls()
    assignments, markings, partial, inconsistent = phase_controls()
    subsets, cosets, translate_families = affine_translate_controls()
    print(f'Rigid groupoid controls passed: {arrows} actual arrows/{products} compositions, '
          f'{families} dominant subgroup-family menus; {menus} invariant relation menus/{factors} rigid factors; '
          f'{saturated} saturated relations/{bridges} quotient bridges/{quotient_products} quotient products; '
          f'{assignments} full phase assignments/{markings} seed markings, {partial} prescribed triples '
          f'({inconsistent} inconsistent); {subsets} nonempty sets/{cosets} affine cosets, '
          f'{translate_families} pairwise-intersecting translate families. '
          'Gate exactness remains a separate hypothesis. '
          'No finite snapshot certifies CCO/AP/SAP or RAW exact descent.')


def main():
    run_controls()


if __name__ == '__main__':
    main()
