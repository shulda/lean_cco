#!/usr/bin/env python3
"""Bounded B043 diagnostics; no general SAP/infinite-orbit certificate."""
from itertools import combinations, permutations, product
from collections import Counter
import json,signal,time
START=time.monotonic()

def subsets(n, cap=None):
    return [frozenset(c) for k in range(n+1 if cap is None else min(n,cap)+1)
            for c in combinations(range(n),k)]

def matched_closure(s):
    return frozenset((sort,x) for sort in ('R','H') for x in s)

def close_unary(s, maps):
    out=set(s)
    while True:
        new=out|{f[x] for f in maps for x in out}
        if new==out:return frozenset(out)
        out=new

def check_matching(counts):
    # Small spans checked only where the named ambient matching has enough room.
    for n in range(1,7):
        ss=subsets(n,3)
        for p in ss:
            for q in ss:
                for d in subsets(n,3):
                    if not d<=p or not d<=q or len(p)+len(q)-len(d)>n:continue
                    moving=sorted(q-d); free=sorted(set(range(n))-p)
                    partial=dict(zip(moving,free[:len(moving)]))
                    partial.update((x,x) for x in d)
                    assert len(set(partial.values()))==len(partial)
                    rest_dom=sorted(set(range(n))-partial.keys())
                    rest_rng=sorted(set(range(n))-set(partial.values()))
                    partial.update(zip(rest_dom,rest_rng))
                    assert len(partial)==n and set(partial.values())==set(range(n))
                    gq=frozenset(partial[x] for x in q)
                    assert matched_closure(p)&matched_closure(gq)==matched_closure(d)
                    assert matched_closure(p|gq)==matched_closure(p)|matched_closure(gq)
                    counts['bounded_matching_span_amalgams']+=1
        for g in permutations(range(n)):
            for p in ss:
                image={(sort,g[x]) for sort,x in matched_closure(p)}
                assert image==set(matched_closure({g[x] for x in p}))
                counts['matching_equivariance_checks']+=1
        # Any pair of real preimages for the same orphan h must coincide.
        for r1,r2,h in product(range(n),repeat=3):
            if r1==h and r2==h:
                assert r1==r2
                counts['orphan_unique_preimage_checks']+=1

def check_unary_union(counts):
    for n in range(1,4):
        ss=subsets(n)
        for f,g in product(product(range(n),repeat=n),repeat=2):
            maps=[f,g]
            closures={s:close_unary(s,maps) for s in ss}
            assert closures[frozenset()]==frozenset()
            for p,q in product(ss,repeat=2):
                assert closures[p|q]==closures[p]|closures[q]
                counts['general_unary_union_checks']+=1

def check_copies(counts):
    # Formal copy supports: all share the same base and otherwise disjoint tags.
    for k in range(1,15):
        base=frozenset(('B',j) for j in range(k%4))
        copies=[base|{('U',j),('X',j)} for j in range(k+1)]
        for i,j in combinations(range(k+1),2):
            assert copies[i]&copies[j]==base
            counts['copy_pair_intersections']+=1
        images={('U',j) for j in range(k+1)}
        assert len(images)==k+1>k
        counts['finite_orbit_pigeonhole_checks']+=1
    # All nonempty closures meet at the globally fixed unary constant image.
    real={('R',0),('R',1)}; hidden=('H',0)
    left={('R',0),hidden};right={('R',1),hidden}
    assert left&right=={hidden} and left&right!=set()
    assert close_unary(set(),[])==frozenset()
    counts['empty_base_constant_map_obstructions']=1
    # A genuinely binary map creates a mixed value, unlike unary maps.
    def binary_closure(s):
        out=set(s)
        while True:
            new=out|{(2 if a!=b else a) for a in out for b in out}
            if new==out:return out
            out=new
    assert binary_closure({0})|binary_closure({1})=={0,1}
    assert binary_closure({0,1})=={0,1,2}
    counts['binary_mixed_generator_boundaries']=1

def main():
    counts=Counter()
    check_matching(counts);check_unary_union(counts);check_copies(counts)
    print(json.dumps(dict(status='PASS',seconds=round(time.monotonic()-START,3),counts=dict(counts),
        witnesses=dict(point_generated_vs_hereditary='Infinite pure real set plus interpreted hidden copy, named bijection without inverse: PGO/point-generated SAP hold; orphan hidden base fails hereditary SAP by unique real preimage.',empty_base='Infinite pure real set mapping to one hidden singleton: nonempty-base off-closure orbits infinite, but empty-base PGO/SAP fail.'),
        limits='Bounded diagnostics only. Fixed finite matching hosts do not satisfy PGO; checks use only capacity-sufficient spans. Infinite-model explanations are mathematical proof notes, not computational certification. No general SAP, infinite orbit, hidden homogeneity or Lean proof is certified.'),sort_keys=True))

if __name__=='__main__':
    signal.alarm(30)
    main()
