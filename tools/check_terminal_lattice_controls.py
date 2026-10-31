#!/usr/bin/env python3
"""Bounded B050 lattice, quotient-power/reset and positive-layer diagnostics.

Finite windows supply only the stated bounded witnesses. No general CCO,
SAP, finite modular lattice theorem or Lean theorem is certified here.
"""
from collections import Counter
from itertools import combinations, permutations, product
import json, signal, time

START=time.monotonic(); C=Counter()

def need(p,msg):
    if not p:raise AssertionError(msg)

def comp(R,S):
    left={}
    for y,z in S:left.setdefault(y,set()).add(z)
    return frozenset((x,z) for x,y in R for z in left.get(y,()))

def diag(n):return frozenset((x,x) for x in range(n))
def top(n):return frozenset(product(range(n),repeat=2))
def strong(R,S):return frozenset((x,z) for x,y in R for u,z in S if y==u and len({x,y,z})==3)

def f3_model():
    pts=tuple(product(range(3),repeat=2)); pos={x:i for i,x in enumerate(pts)}
    def neg(v):return tuple((-x)%3 for x in v)
    def colour(x,y):
        d=tuple((b-a)%3 for a,b in zip(x,y));return min(d,neg(d))
    atoms=sorted({colour(x,y) for x in pts for y in pts if x!=y})
    # Every normalized partial isomorphism fixes 0, hence may send x only
    # to +/-x. Exhaust all subsets and these candidates, including all sizes.
    zero=(0,0);rest=[p for p in pts if p!=zero]
    for choice in product((0,1,2),repeat=len(rest)):
        pairs=[(zero,zero)]+[(x,x if c==1 else neg(x)) for x,c in zip(rest,choice) if c]
        C['normalized_partial_map_candidates']+=1
        if len({y for x,y in pairs})<len(pairs):continue
        if any(colour(x,y)!=colour(u,v) for (x,u),(y,v) in combinations(pairs,2)):continue
        need(any(all(u==(x if s==1 else neg(x)) for x,u in pairs) for s in (1,-1)),
             'actual F3^2 partial isomorphism lacks +/- extension')
        C['all_size_partial_isomorphism_extensions']+=1
    relations=[]
    for mask in range(1<<len(atoms)):
        R=diag(9)|frozenset((i,j) for i,x in enumerate(pts) for j,y in enumerate(pts)
                           if i!=j and mask&(1<<atoms.index(colour(x,y))))
        if comp(R,R)<=R:relations.append(R)
    need(len(relations)==6,'F3^2 invariant lattice must have four lines plus endpoints')
    lo,hi=diag(9),top(9);lines=[R for R in relations if R not in (lo,hi)]
    for E,F,G in product(relations,repeat=3):
        need(comp(E,F)==comp(F,E),'symmetric same-sort RAW commutation')
        if E<=G:need(comp(E,F)&G==comp(E,F&G),'modular equivalence law')
        l=(E&F)|(F&G)|(G&E)
        # Convert lattice union to actual equivalence join.
        l=comp(comp(E&F,F&G),G&E)
        h=comp(E,F)&comp(F,G)&comp(G,E)
        aa=comp(E,l)&h;bb=comp(F,l)&h;cc=comp(G,l)&h
        for X,Y in [(aa,bb),(aa,cc),(bb,cc)]:
            need(X&Y==l and comp(X,Y)==h,'modular median normalization')
        nondist=(E&comp(F,G))!=comp(E&F,E&G)
        if nondist:need(l<h,'nondistributive witness must make genuine diamond')
        C['modular_median_triples']+=1
    for E,F in product(relations,repeat=2):
        if E<F and not any(E<H<F for H in relations):
            x=0;upper={y for a,y in F if a==x};blocks={frozenset(y for a,y in E if a==z) for z in upper}
            need(len(blocks)==3,'all F3^2 full covers have index three, not two')
            C['actual_full_covers_index_three']+=1
    # Build the source's actual seven-edge M3 obstruction with 3 private
    # two-letter word paths, plus the complete old fine centre pair.
    E1,E2,E3=lines[:3]
    x=0;y=next(z for a,z in E1 if a==x and z!=x)
    dirs=[]
    for E in (E1,E2,E3):dirs.append(colour(pts[0],pts[next(z for a,z in E if a==0 and z!=0)]))
    edges={(0,3):dirs[0],(1,3):dirs[0],(0,4):dirs[1],(1,4):dirs[1],
           (0,5):dirs[2],(2,5):dirs[2],(1,2):colour(pts[x],pts[y])}
    def hom(n,es,pinned=None):
        values=dict(pinned or {});order=[i for i in range(n) if i not in values]
        def go(k):
            if k==len(order):return dict(values)
            a=order[k]
            for v in range(9):
                if any(tuple(sorted((a,b))) in es and colour(pts[v],pts[w])!=es[tuple(sorted((a,b)))]
                       for b,w in values.items()):continue
                values[a]=v;r=go(k+1)
                if r is not None:return r
                del values[a]
            return None
        return go(0)
    need(hom(6,edges,{1:x,2:y}) is None,'actual complete-centre M3 network must fail globally')
    for size in range(3,7):
        for sub in combinations(range(6),size):
            for tail in permutations(sub[1:]):
                if tail[0]>tail[-1]:continue
                cyc=(sub[0],)+tail;pairs=[tuple(sorted((cyc[i],cyc[(i+1)%size]))) for i in range(size)]
                if not all(e in edges for e in pairs):continue
                es={tuple(sorted((i,(i+1)%size))):edges[e] for i,e in enumerate(pairs)}
                need(hom(size,es) is not None,'every specified M3 simple cycle must be feasible')
                C['actual_M3_feasible_simple_cycles']+=1
    C['actual_M3_global_failures']+=1
    # RAW line words really have length two and include true identity.
    for E in lines:
        t=E-lo;need(comp(t,t)==E,'line relation must be its diversity atom squared')
        C['actual_RAW_line_words']+=1


def quotient_powers_and_phi():
    for n in (2,3,5,7):
        D=diag(n);U=top(n);T=frozenset((x,y) for x in range(n) for y in range(n)
                                    if (x-y)%n in (1,n-1))
        P=D;full_at=None
        for k in range(1,2*n+3):
            P=comp(P,T)
            if n==2:need(P==(T if k%2 else D),'index-two powers alternate')
            else:
                if P==U and full_at is None:full_at=k
                if full_at is not None:need(P==U,'aperiodic powers remain full')
            C['actual_quotient_graph_powers']+=1
        if n>2:need(full_at is not None,'odd connected quotient eventually reaches top')
    # Non-full cover boundary: C4 has a nontrivial even-walk equivalence.
    T=frozenset((x,y) for x in range(4) for y in range(4) if (x-y)%4 in (1,3))
    need(diag(4)<comp(T,T)<top(4),'C4 must violate the full-cover premise')
    C['nonfull_cover_bipartite_guard']+=1
    # Phi uses complete pullbacks and at least 3 clones, including quotient
    # diagonal. Only 3-vertex products are asserted for these finite windows.
    n=5;D=diag(n)
    R=frozenset((x,y) for x in range(n) for y in range(n) if (x-y)%n in (1,4))
    B=top(n)-D-R;atoms=(D,R,B);width=4;size=n*width
    menus=[frozenset().union(*(a for i,a in enumerate(atoms) if mask&(1<<i)))
           for mask in range(8)]
    def phi(Q):return frozenset((x,y) for x in range(size) for y in range(size)
                              if x!=y and (x//width,y//width) in Q)
    images=[phi(Q) for Q in menus];need(len(set(images))==8,'Phi is injective even on diagonal relation')
    for A,E in product(menus,repeat=2):
        need(phi(A&E)==phi(A)&phi(E),'Phi intersections')
        need(phi(A|E)==phi(A)|phi(E),'Phi unions')
        if A and E:need(strong(phi(A),phi(E))==phi(comp(A,E)),'exact quotient STRONG product lifting')
        C['actual_Phi_menu_pairs']+=1
    # Narrow same-J saturation used by reset/layer, with all old fine atoms.
    J=frozenset((x,y) for x in range(size) for y in range(size) if x//width==y//width)
    Jc=J-diag(size)
    for t in (Jc,phi(R),phi(B)):
        raw=comp(comp(J,t),J)-diag(size)
        got=frozenset((x,y) for x,u in Jc for v,y in Jc
                      if (u,v) in t and len({x,u,v,y})==4)
        need(raw==got,'same-J RAW saturation needs genuinely distinct OLD vertices')
        C['same_J_pinned_saturation_cases']+=1
    # C5 is primitive with eventual powers but not reset: this is outside
    # CCO, so primitive/full-cover alone must never supply the reset theorem.
    need(comp(R,R)!=top(5) and comp(B,B)!=top(5),'CCO-free reset overclaim guard')
    C['without_CCO_reset_guard']+=1


def cycle_guard_controls():
    # Infinite clone cover of C5 supplies quotient walks; sufficiently large
    # finite clone indices give distinct real witnesses only for these cycles.
    n=5;red=frozenset((x,y) for x in range(n) for y in range(n) if (x-y)%n in (1,4))
    blue=top(n)-diag(n)-red
    H=9;N=4;r=2;need(H>r*(N-1)+1,'girth/pigeonhole threshold')
    labels=[1 if i%2==0 else 2 for i in range(H)]
    def close_word(word):
        paths={0:[0]}
        for lab in word:
            nxt={}
            rel=red if lab==1 else blue
            for x,path in paths.items():
                for a,y in rel:
                    if a==x and y not in nxt:nxt[y]=path+[y]
            paths=nxt
        need(0 in paths,'specified expanded cycle has no actual quotient walk')
        path=paths[0];used=Counter();old=[]
        for q in path[:-1]:old.append((q,used[q]));used[q]+=1
        need(len(set(old))==len(old),'fresh OLD clone representatives')
        old.append(old[0])
        for i,lab in enumerate(word):
            need((old[i][0],old[i+1][0]) in (red if lab==1 else blue),'actual OLD edge witness')
        C['guarded_actual_cycle_walks']+=1
        C['guarded_real_cycle_vertices']+=len(word)
    close_word(labels)
    # Every star-visited simple root cycle is two spokes plus one of the two
    # simple H-paths between distinct H-vertices. Spoke word is red^4=Top.
    for a,b in combinations(range(H),2):
        clockwise=[labels[i%H] for i in range(a,b)]
        other=[labels[i%H] for i in range(b,a+H)]
        close_word([1]*4+clockwise+[1]*4)
        close_word([1]*4+other+[1]*4)
    close_word([1]*8)  # two private theta branches with common menu


def formal_layer_control():
    # Actual random-graph quotient orbital table, checked by all 8 possible
    # complete two-colour triangles. This is a bounded table diagnostic;
    # no finite window is declared to be the countable homogeneous source.
    I,A,B=1,2,4;U=A|B;TOP=I|U
    table={(I,I):I,(I,A):A,(A,I):A,(I,B):B,(B,I):B,
           (A,A):TOP,(B,B):TOP,(A,B):U,(B,A):U}
    def mul(x,y):return sum_or(table[a,b] for a in (I,A,B) if x&a for b in (I,A,B) if y&b)
    for edges in product((A,B),repeat=3):
        a,b,c=edges;need(table[a,c]&b,'every actual random-graph triangle is permitted')
        C['complete_two_colour_triangle_types']+=1
    for a,b,c in product(range(1,8),repeat=3):
        need(mul(mul(a,b),c)==mul(a,mul(b,c)),'full represented associativity')
        C['formal_orbital_associativity_checks']+=1
    need(mul(A,A)==TOP and mul(B,B)==TOP,'actual reset complete orbitals')
    need(mul(A,B)==U,'distinct complete orbitals give ONE external layer word')
    C['positive_external_layer_word']+=1


def sum_or(items):
    out=0
    for x in items:out|=x
    return out


def main():
    f3_model();quotient_powers_and_phi();cycle_guard_controls();formal_layer_control()
    print(json.dumps(dict(status='PASS',seconds=round(time.monotonic()-START,3),counts=dict(sorted(C.items())),
        witnesses=dict(nonSAP_NR2_M3_model='F3^2 with four undirected direction atoms',
                       full_cover_needed='C4 even-walk equivalence',CCO_needed_for_reset='C5 quotient',
                       quotient_diagonal_not_old_diversity_identity=True),
        limits='Bounded actual finite models/witnesses and small table checks only. No fixed finite clone window is certified unbounded SAP/CCO; no general modular M3 criterion, sparse labelled graph existence, original reset/layer theorem or Lean proof is certified.'),sort_keys=True))

if __name__=='__main__':
    signal.alarm(30);main()
