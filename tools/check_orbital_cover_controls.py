#!/usr/bin/env python3
"""Bounded B046 actual product/coordinate/diagonal-orientation diagnostics.

Finite windows are witness oracles for diagrams of size at most four, not
models claimed to have unbounded CCO/SAP. No Lean proof is certified.
"""
from collections import Counter, defaultdict, deque
from functools import lru_cache
from itertools import combinations, permutations, product
import json,signal,time

START=time.monotonic()
E0,E1,N=0,1,2
C=Counter()

def demand(p,msg):
    if not p:raise AssertionError(msg)

def one_col(a,b):
    return a[1]^b[1] if a[0]==b[0] else N

def col(a,b):
    demand(a!=b,'diversity input must be distinct real points')
    return (one_col((a[0],a[2]),(b[0],b[2])),
            one_col((a[1],a[3]),(b[1],b[3])))

def table(a,b):
    if a==N and b==N:return {E0,E1,N}
    if a==N or b==N:return {N}
    return {a^b}

@lru_cache(None)
def cycles(n):
    out=[]
    for size in range(3,n+1):
        for subset in combinations(range(n),size):
            first=min(subset)
            for tail in permutations(tuple(x for x in subset if x!=first)):
                if tail[0]<tail[-1]:out.append((first,)+tail)
    return tuple(out)

def edge_map(n,labels):return dict(zip(combinations(range(n),2),labels))
def at(edges,a,b):return edges[tuple(sorted((a,b)))]

@lru_cache(None)
def cycle_ok(word):
    # Independent finite actual walk oracle: coordinate e0 permits repeated
    # coordinate values; distinct real vertices can use fresh clone indices.
    states=tuple(product(range(len(word)),range(2)))
    for start in states:
        seen={start}
        for label in word:
            seen={q for p in seen for q in states if one_col(p,q)==label}
        if start in seen:return True
    return False

def old_cycles_ok(n,labels):
    edges=edge_map(n,labels)
    for cyc in cycles(n):
        word=tuple(at(edges,cyc[i],cyc[(i+1)%len(cyc)]) for i in range(len(cyc)))
        if None not in word and not cycle_ok(word):return False
    return True

def potential_solve(n,labels,marks=None):
    edges=edge_map(n,labels);adj=[[] for _ in range(n)]
    for (a,b),label in edges.items():
        if label in (E0,E1):adj[a].append((b,label));adj[b].append((a,label))
    comp=[None]*n;bits=[None]*n;k=0
    for root in range(n):
        if comp[root] is not None:continue
        comp[root]=k;bits[root]=marks[root] if marks is not None else 0
        todo=deque([root])
        while todo:
            a=todo.popleft()
            if marks is not None and bits[a]!=marks[a]:return None
            for b,s in adj[a]:
                bit=bits[a]^s
                if comp[b] is None:comp[b]=k;bits[b]=bit;todo.append(b)
                elif bits[b]!=bit:return None
        k+=1
    for (a,b),label in edges.items():
        if label==N and comp[a]==comp[b]:return None
    return tuple(zip(comp,bits))

def brute_hom(n,labels,marks=None):
    # Independent direct backtracking into n blocks x F2, sufficient for
    # n-vertex tests. No component/potential information is used here.
    edges=edge_map(n,labels);states=tuple(product(range(max(1,n)),range(2)));values=[]
    def visit(i):
        if i==n:return tuple(values)
        for q in states:
            if marks is not None and q[1]!=marks[i]:continue
            if any(at(edges,j,i) is not None and one_col(p,q)!=at(edges,j,i)
                   for j,p in enumerate(values)):continue
            values.append(q);got=visit(i+1)
            if got is not None:return got
            values.pop()
        return None
    return visit(0)

def actual_products():
    real=tuple(product(range(3),range(3),range(2),range(2),range(3)))
    x=real[0];observed=defaultdict(set)
    for y in real:
        if y==x:continue
        for z in real:
            if z in (x,y):continue
            observed[col(x,y),col(y,z)].add(col(x,z));C['actual_distinct_vertex_triangles']+=1
    colours=tuple(product(range(3),repeat=2))
    for a,b in product(colours,repeat=2):
        expected=set(product(table(a[0],b[0]),table(a[1],b[1])))
        demand(observed[a,b]==expected,'actual nine-colour strong product differs')
        C['nine_colour_product_entries']+=1
    # RAW diagonal output and diversity clone atom are genuinely different.
    y=(0,0,0,0,1)
    demand(col(x,y)==(E0,E0),'clone diversity atom')
    demand(x==x and y!=x,'Id is not clone diversity')
    C['logical_identity_clone_atom_guard']+=1


def coordinate_and_triangle_controls():
    # All single-coordinate partial diagrams, including disconnected ones.
    for n in range(5):
        for labels in product((None,E0,E1,N),repeat=n*(n-1)//2):
            cyclic=old_cycles_ok(n,labels);sol=potential_solve(n,labels);oracle=brute_hom(n,labels)
            demand((sol is not None)==cyclic,'cycle/potential criterion')
            demand((oracle is not None)==cyclic,'independent actual homomorphism oracle')
            C['coordinate_partial_diagrams']+=1
            if sol is not None:
                edges=edge_map(n,labels)
                demand(all(label is None or one_col(sol[a],sol[b])==label
                           for (a,b),label in edges.items()),'whole coordinate witness')
            if n<=3:
                for marks in product(range(2),repeat=n):
                    marked=potential_solve(n,labels,marks);direct=brute_hom(n,labels,marks)
                    demand((marked is not None)==(direct is not None),'prescribed p/q marked solver')
                    C['prescribed_coordinate_markings']+=1
    # Complete nine-colour triangles: direct two independent coordinate
    # solutions must agree with the actual strong product table.
    colours=tuple(product(range(3),repeat=2))
    for labels in product(colours,repeat=3):
        l0=tuple(a[0] for a in labels);l1=tuple(a[1] for a in labels)
        actual=(brute_hom(3,l0) is not None and brute_hom(3,l1) is not None)
        a,b,c=labels  # edges01,02,12; output02 lies in input01*input12
        typed=(b[0] in table(a[0],c[0]) and b[1] in table(a[1],c[1]))
        demand(actual==typed,'complete triangle table is actual')
        C['complete_nine_colour_triangles']+=1
    # An n-edge inside one signed component and a signed odd cycle are
    # different cycle obstructions; test both explicitly.
    demand(not old_cycles_ok(3,(E0,N,E1)),'n inside e-component must fail')
    demand(not old_cycles_ok(3,(E1,E1,E1)),'odd signed e cycle must fail')
    C['independent_cycle_obstruction_guards']+=2


def orientation_controls():
    colours=tuple(product(range(3),repeat=2))
    left=set(product(table(E0,E0),table(N,N)))
    right=set(product(table(N,N),table(E0,E0)))
    demand(left&right=={(E0,E0)},'cross-support intersection')
    for hs in product(range(2),repeat=4):
        h={(0,0):hs[0],(0,1):hs[1],(1,0):hs[2],(1,1):hs[3]}
        def phase(x):return x[2]^x[3]^h[x[0],x[1]]
        d=(1,1,h[1,1],0,4)
        bs=[(0,0,e,e^h[0,0],e) for e in range(2)]
        zs=[(0,1,e,0,e+2) for e in range(2)]
        for e in range(2):
            demand(phase(bs[e])==phase(d)==0,'marked base phases')
            demand(col(bs[e],d)==(N,N),'base type')
            demand(col(bs[e],zs[e])==(E0,N),'left triangle edge')
            demand(col(zs[e],d)==(N,E0),'right triangle edge')
            demand(phase(zs[e])==e^h[0,1],'new vertex phase')
        demand(phase(zs[0])!=phase(zs[1]),'opposite bits prohibit Id collision')
        # Any distinct candidate pair compatible with both paths must be
        # clone-equal, whence K-constancy forbids those opposite bits.
        owners=tuple(product(range(2),range(2),range(2),range(2)))
        for x,y in product(owners,repeat=2):
            k=(x[:2]==y[:2] and (x[2]^x[3])==(y[2]^y[3]))
            if k:demand(phase(x+(0,))==phase(y+(1,)),'orientation constant on all K-blocks')
            C['K_constancy_pairs']+=1
        C['all_rectangle_orientations']+=1
        C['opposite_mark_identity_guards']+=1
    # Diagonal palette cannot be a box, while finer one-coordinate palettes
    # are boxes and explicit compatible labels p then q orient them.
    diag={(E0,E0),(E1,E1)}
    box=set(product({x[0] for x in diag},{x[1] for x in diag}))
    demand(diag!=box,'bad K is not a reachable box')
    real=tuple(product(range(2),range(2),range(2),range(2),range(2)))
    for fixed in ('p','q'):
        # Quotient the clone fibres (K0) inside each actual fine-cover class.
        classes=defaultdict(list)
        for x in real:
            key=(x[0],x[1],x[3]) if fixed=='p' else (x[0],x[1],x[2])
            classes[key].append(x)
        for members in classes.values():
            by_owner=defaultdict(list)
            for x in members:by_owner[x[:4]].append(x)
            demand(len(by_owner)==2,'fine interval has exactly two K0 blocks')
            labels=[]
            for block in by_owner.values():
                bits={x[2] if fixed=='p' else x[3] for x in block}
                demand(len(bits)==1,'fine orientation constant on K0')
                labels.append(next(iter(bits)))
            demand(set(labels)=={0,1},'the two fine blocks get opposite labels')
            C['explicit_fine_cover_classes']+=1
    C['nonbox_diagonal_guard']+=1


def main():
    actual_products();coordinate_and_triangle_controls();orientation_controls()
    print(json.dumps(dict(status='PASS',seconds=round(time.monotonic()-START,3),counts=dict(sorted(C.items())),
        witnesses=dict(all_h_rectangle_values_checked=16,logical_Id_separate_from_clone_e0e0=True,
                       complete_diagram_scope='actual finite-window constraint witnesses',
                       fine_split_scope='explicit compatible p then q only'),
        limits='Bounded diagnostics only. No fixed finite host is claimed to have unbounded CCO/SAP; no general parity/Hasse, infinite automorphism-extension theorem or Lean proof is certified.'),sort_keys=True))

if __name__=='__main__':
    signal.alarm(30);main()
