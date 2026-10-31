#!/usr/bin/env python3
"""Bounded independent code/coordinate/block-order diagnostics for B061.

These finite checks are not proofs of Ramsey, CCO, HN or terminalisation.
They enumerate actual map sets, rather than replaying the module DAG.
"""
from itertools import combinations, permutations, product
import json


SORTS = ('R', 'C', 'T')
PRIORITY = {'C': 0, 'R': 1, 'T': 2}


def subsets(items):
    items = tuple(items)
    for size in range(len(items) + 1):
        yield from combinations(items, size)


class Host:
    """Three named sorts, an inverse R<->T transition, and a binary atom.

    A valid root is the literal pair (R_i,C_j). Terms also see T_i=F(R_i).
    Its actual fine reduct is encoded by the complete hidden full code;
    no particular CCO or homogeneity theorem is assumed in this diagnostic.
    """
    def __init__(self, rows, cols, order=None):
        self.rows = tuple(rows)
        self.cols = tuple(cols)
        self.points = tuple(('R', i) for i in self.rows) + tuple(('C', j) for j in self.cols) + tuple(('T', i) for i in self.rows)
        self.order = tuple(self.points if order is None else order)
        assert set(self.order) == set(self.points)
        self.rank = {p: n for n, p in enumerate(self.order)}
        self.roots = tuple(product(self.rows, self.cols))

    def fn(self, name, point):
        if name == 'F' and point[0] == 'R':
            return ('T', point[1])
        if name == 'G' and point[0] == 'T':
            return ('R', point[1])
        return None

    def rel(self, x, y):
        # One directed named binary predicate; negative instances are tested.
        return x[0] == 'R' and y[0] == 'C' and (x[1] + y[1]) % 2 == 0

    def less(self, x, y):
        return self.rank[x] < self.rank[y]

    def terms(self, root):
        r, c = root
        return (('R', r), ('C', c), ('T', r))

    def pair_code(self, left, right):
        # Full same-root and cross-root term codes, including every order pair.
        xs, ys = self.terms(left), self.terms(right)
        return tuple((x == y, self.rel(x, y), self.less(x, y),
                      self.fn('F', x) == y, self.fn('G', x) == y)
                     for x in xs for y in ys)

    def support(self, roots):
        rows = tuple(sorted({r for r, _ in roots}))
        cols = tuple(sorted({c for _, c in roots}))
        return {('R', i) for i in rows} | {('C', j) for j in cols} | {('T', i) for i in rows}

    def completion(self, roots):
        rows = tuple(sorted({r for r, _ in roots}))
        cols = tuple(sorted({c for _, c in roots}))
        return tuple(product(rows, cols))

    def block(self):
        order = tuple(sorted(self.order, key=lambda p: PRIORITY[p[0]]))
        return Host(self.rows, self.cols, order)

    def restriction(self, rows, cols):
        keep = {('R', i) for i in rows} | {('C', j) for j in cols} | {('T', i) for i in rows}
        return Host(rows, cols, (p for p in self.order if p in keep))


def visible_maps(source, roots, target):
    """Enumerate injections of literal ROOTS and compare complete codes."""
    roots = tuple(roots)
    result = set()
    for images in permutations(target.roots, len(roots)):
        mapping = dict(zip(roots, images))
        if all(source.pair_code(a, b) == target.pair_code(mapping[a], mapping[b])
               for a in roots for b in roots):
            result.add(images)
    return result


def hidden_maps(source, support, target):
    """Independently enumerate sorted HIDDEN injections and their semantics."""
    support = tuple(sorted(support))
    by_sort = {s: tuple(x for x in support if x[0] == s) for s in SORTS}
    targets = {s: tuple(x for x in target.points if x[0] == s) for s in SORTS}
    choices = [tuple(permutations(targets[s], len(by_sort[s]))) for s in SORTS]
    for images in product(*choices):
        mapping = {p: q for s, qs in zip(SORTS, images) for p, q in zip(by_sort[s], qs)}
        if any((source.fn(f, p) is None) != (target.fn(f, mapping[p]) is None)
               for f in ('F', 'G') for p in support):
            continue
        if any(mapping[source.fn(f, p)] != target.fn(f, mapping[p])
               for f in ('F', 'G') for p in support if source.fn(f, p) is not None):
            continue
        if any(source.rel(p, q) != target.rel(mapping[p], mapping[q])
               or source.less(p, q) != target.less(mapping[p], mapping[q])
               for p in support for q in support):
            continue
        yield mapping


def candidate_orders(points):
    points = tuple(points)
    candidates = [points, points[::-1], tuple(sorted(points)),
                  tuple(sorted(points, key=lambda p: (p[1], p[0]))),
                  tuple(sorted(points, key=lambda p: (PRIORITY[p[0]], -p[1])))]
    return tuple(dict.fromkeys(candidates))


def check_bijections_and_completion():
    templates = []
    for nr, nc in product(range(3), repeat=2):
        h = Host(range(nr), range(nc))
        templates.extend(Host(h.rows, h.cols, order) for order in candidate_orders(h.points))
    cases = total_visible = completions = empty_cases = orphan_cases = normalized_maps = 0
    for source in templates:
        for roots in subsets(source.roots):
            support = source.support(roots)
            completed = source.completion(roots)
            assert set(roots) <= set(completed)
            assert source.support(completed) == support
            assert source.completion(completed) == completed
            assert len(support) <= 3 * len(roots)
            assert len(completed) <= len(source.points) ** 2
            completions += 1
            for target in templates:
                visible = visible_maps(source, roots, target)
                hidden = list(hidden_maps(source, support, target))
                induced = {tuple((g[('R', r)][1], g[('C', c)][1]) for r, c in roots)
                           for g in hidden}
                assert visible == induced, (source.order, roots, target.order, visible, induced)
                assert len(hidden) == len(induced), 'The hidden extension must be unique over marked roots'
                cases += 1
                total_visible += len(visible)
                empty_cases += not roots
                orphan_cases += bool(set(target.points) - target.support(target.roots))
                for g in hidden:
                    images = tuple((g[('R', r)][1], g[('C', c)][1]) for r, c in completed)
                    assert len(set(images)) == len(completed)
                    assert set(images) <= set(target.completion(target.roots))
                    assert source.support(completed) == support
                    # The same actual hidden map stays induced after block normalization.
                    sb, tb = source.block(), target.block()
                    assert all(sb.less(p, q) == tb.less(g[p], g[q]) for p in support for q in support)
                    normalized_maps += 1
    assert cases > 1000 and total_visible > 1000 and empty_cases and orphan_cases
    return dict(embedding_bijections=cases, actual_embedding_maps=total_visible,
                selected_root_completions=completions, empty_root_hosts=empty_cases,
                orphan_host_cases=orphan_cases, normalized_actual_maps=normalized_maps)


def complete_map(mapping, roots):
    return {root: (mapping[('R', root[0])][1], mapping[('C', root[1])][1]) for root in roots}


def full_coordinate_permutations(host):
    for rp in permutations(host.rows):
        for cp in permutations(host.cols):
            m = {('R', x): ('R', y) for x, y in zip(host.rows, rp)}
            m.update({('T', x): ('T', y) for x, y in zip(host.rows, rp)})
            m.update({('C', x): ('C', y) for x, y in zip(host.cols, cp)})
            if all(host.rel(p, q) == host.rel(m[p], m[q]) for p in host.points for q in host.points):
                yield m


def check_completion_naturality():
    base = Host(range(2), range(2))
    changes = tuple(full_coordinate_permutations(base))
    cases = nonidentity = 0
    for f, g in product(changes, repeat=2):
        middle = Host(base.rows, base.cols, (f[p] for p in base.order))
        last = Host(base.rows, base.cols, (g[p] for p in middle.order))
        assert list(hidden_maps(base, set(base.points), middle))
        assert list(hidden_maps(middle, set(middle.points), last))
        gf = {p: g[f[p]] for p in base.points}
        for roots in subsets(base.roots):
            completed = base.completion(roots)
            cf = complete_map(f, completed)
            cg = complete_map(g, tuple(cf.values()))
            cgf = complete_map(gf, completed)
            assert {a: cg[cf[a]] for a in completed} == cgf
            for a, b in product(completed, repeat=2):
                assert base.pair_code(a, b) == last.pair_code(cgf[a], cgf[b])
            assert base.support(base.completion(roots)) == base.support(roots)
            cases += 1
            nonidentity += any(f[p] != p or g[p] != p for p in base.points)
    assert cases >= 64 and nonidentity
    return dict(natural_completion_compositions=cases, nonidentity_compositions=nonidentity)


def check_nonempty_orphan_host():
    """A qf tuple domain can leave orphans beside a nonempty root set."""
    class ComponentHost(Host):
        def __init__(self, rows, cols, order=None):
            super().__init__(rows, cols, order)
            self.roots = tuple((r, c) for r, c in self.roots if r // 2 == c // 2)

        def rel(self, x, y):
            return x[0] == 'R' and y[0] == 'C' and x[1] // 2 == y[1] // 2

    source = ComponentHost((0,), (0,))
    target = ComponentHost((0, 1, 2), (0, 1))
    roots = source.roots
    support = source.support(roots)
    orphans = set(target.points) - target.support(target.roots)
    assert target.roots and orphans == {('R', 2), ('T', 2)}
    # The orphan pair is itself closed under BOTH inverse unary functions.
    assert all(target.fn(f, p) in orphans for f, p in [('F', ('R', 2)), ('G', ('T', 2))])
    visible = visible_maps(source, roots, target)
    hidden = list(hidden_maps(source, support, target))
    induced = {tuple((g[('R', r)][1], g[('C', c)][1]) for r, c in roots)
               for g in hidden}
    assert visible == induced and len(hidden) == len(induced) == 4
    assert all(not (set(g.values()) & orphans) for g in hidden)
    return dict(nonempty_orphan_host_maps=len(hidden), closed_orphan_points=len(orphans))


def check_all_block_orders():
    orders = restrictions = same_map_embeddings = 0
    for nr, nc in ((1, 1), (2, 1), (1, 2), (2, 2)):
        raw = Host(range(nr), range(nc))
        changes = tuple(full_coordinate_permutations(raw))
        for order in permutations(raw.points):
            host = Host(raw.rows, raw.cols, order)
            block = host.block()
            assert block.block().order == block.order
            for row_set, col_set in product(subsets(host.rows), subsets(host.cols)):
                small = host.restriction(row_set, col_set)
                assert small.block().order == block.restriction(row_set, col_set).order
                restrictions += 1
            for mapping in changes:
                target = Host(raw.rows, raw.cols, (mapping[p] for p in host.order))
                assert all(host.less(p, q) == target.less(mapping[p], mapping[q])
                           for p in host.points for q in host.points)
                target_block = target.block()
                assert all(block.less(p, q) == target_block.less(mapping[p], mapping[q])
                           for p in host.points for q in host.points)
                same_map_embeddings += 1
            # Every omitted different-target comparison has its forced priority value.
            assert all(block.less(p, q) == (PRIORITY[p[0]] < PRIORITY[q[0]])
                       for p in block.points for q in block.points if p[0] != q[0])
            orders += 1
    assert orders == 870 and restrictions > 10000 and same_map_embeddings > 1000
    return dict(exhaustive_global_orders=orders, closed_block_restrictions=restrictions,
                block_same_map_embeddings=same_map_embeddings)


def check_boundaries():
    # One root: an off-diagonal-visible-only code has NO comparisons at all.
    root = (0, 0)
    first = Host((0,), (0,), (('R', 0), ('C', 0), ('T', 0)))
    second = Host((0,), (0,), (('C', 0), ('R', 0), ('T', 0)))
    assert first.pair_code(root, root) != second.pair_code(root, root)
    assert visible_maps(first, (root,), second) == set()
    assert not [(a, b) for a in (root,) for b in (root,) if a != b]

    # Shared-coordinate witness in the UNORDERED generic reconstruction interface.
    # There are no hidden binary relations/functions in this separate two-sort model.
    # If all strict-order pairs were kept, equality could instead be definable from
    # the two order directions; we do not claim that E alone is then indispensable.
    source_roots = ((('R', 0), ('C', 0)), (('R', 0), ('C', 1)))
    target_roots = ((('R', 0), ('C', 0)), (('R', 1), ('C', 1)))
    assert all(tuple(p[0] for p in a) == tuple(p[0] for p in b)
               for a, b in zip(source_roots, target_roots))
    assert source_roots[0][0] == source_roots[1][0]
    assert target_roots[0][0] != target_roots[1][0]
    assert all((a[0] == a[1]) == (b[0] == b[1]) for a, b in zip(source_roots, target_roots))
    # A term-preserving extension would send the same R_0 to two different points.
    proposed_images = {target_roots[i][0] for i in range(2)}
    assert len(proposed_images) == 2

    # Different VISIBLE tags can still have their terms in one HIDDEN target sort.
    tagged_roots = (('visible_s', ('R', 0)), ('visible_t', ('R', 1)))
    left_order = Host((0, 1), (), (('R', 0), ('R', 1), ('T', 0), ('T', 1))).block()
    right_order = Host((0, 1), (), (('R', 1), ('R', 0), ('T', 0), ('T', 1))).block()
    u, v = tagged_roots[0][1], tagged_roots[1][1]
    assert u[0] == v[0] and tagged_roots[0][0] != tagged_roots[1][0]
    assert left_order.less(u, v) != right_order.less(u, v)
    return dict(diagonal_order_boundary=1, unordered_shared_coordinate_boundary=1,
                different_visible_same_target_boundary=1)


def main():
    result = {}
    result.update(check_bijections_and_completion())
    result.update(check_completion_naturality())
    result.update(check_nonempty_orphan_host())
    result.update(check_all_block_orders())
    result.update(check_boundaries())
    result['status'] = 'PASS_BOUNDED_DIAGNOSTICS_ONLY'
    print(json.dumps(result, sort_keys=True))


if __name__ == '__main__':
    main()
