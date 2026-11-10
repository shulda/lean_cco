#!/usr/bin/env python3
"""Finite FG/LEX controls, not a mathematical Lean proof."""
from itertools import combinations, permutations

PAL = frozenset(range(3))
STAGES = (frozenset({frozenset({0, 1})}), frozenset({frozenset({0})}))


def gate(family, domain):
    active = [a for a in family if a & domain]
    result = domain
    for a in active:
        result = result & a
    return result


def weight(family, a):
    return sum(a in f for f in family)


def check():
    original = [frozenset(c) for n in range(1, 4) for c in combinations(PAL, n)]
    for family in STAGES:
        for d in original:
            survivor = gate(family, d)
            assert survivor
            maximum = max(weight(family, a) for a in d)
            assert survivor == frozenset(a for a in d if weight(family, a) == maximum)
            for a in survivor:
                for b in d - survivor:
                    assert weight(family, a) > weight(family, b)
    scores = {a: tuple(weight(f, a) for f in STAGES) for a in PAL}
    assert scores[0] > scores[1] > scores[2]
    for d in original:
        result = d
        for f in STAGES:
            result = gate(f, result)
            assert result
        best = max(scores[a] for a in d)
        assert result == frozenset(a for a in d if scores[a] == best)
        assert len(result) == 1
    # Independent set-theoretic heredity does not prohibit cyclic revealed
    # preferences, so it cannot imply a universal priority theorem.
    wins = {(0, 1): 0, (1, 2): 1, (0, 2): 2}
    assert not any(all(order.index(win) < order.index(pair[1] if pair[0] == win else pair[0])
                       for pair, win in wins.items()) for order in permutations(PAL))
    return 'FG/LEX 7 nonempty menus + zero/active filters and cyclic-HS negative control PASS; no Lean proof claimed'


if __name__ == '__main__':
    print(check())
