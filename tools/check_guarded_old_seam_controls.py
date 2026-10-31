#!/usr/bin/env python3
"""Bounded B057 diagnostics; no infinite SAP/CCO or forest certificate."""
from itertools import product,combinations
from collections import deque

X=list(product(range(3),range(3),range(3)))
PALETTE=frozenset(['p','r','c','d']);ALL=PALETTE|{'Id'}
def atom(x,y):
    if x==y:return 'Id'
    if x[:2]==y[:2]:return 'p'
    if x[0]==y[0]:return 'r'
    if x[1]==y[1]:return 'c'
    return 'd'
RAW={(a,b):set() for a,b in product(ALL,repeat=2)}
STRONG={(a,b):set() for a,b in product(PALETTE,repeat=2)}
for x,y,z in product(X,repeat=3):
    a,b,t=atom(x,y),atom(y,z),atom(x,z);RAW[a,b].add(t)
    if len({x,y,z})==3:STRONG[a,b].add(t)
def mul(A,B,table=RAW):return frozenset().union(*(table[a,b] for a,b in product(A,B)))
def subsets(S):
    S=sorted(S)
    for n in range(len(S)+1):
        for A in combinations(S,n):yield frozenset(A)
EQ=[frozenset({'Id'}),frozenset({'Id','p'}),frozenset({'Id','p','r'}),frozenset({'Id','p','c'}),ALL]

def word_envelopes():
    seen={};q=deque()
    for a in PALETTE:
        st=(frozenset({a}),frozenset({a}));seen[st]=(a,);q.append(st)
    while q:
        R,e=q.popleft()
        for a in PALETTE:
            nxt=(mul(R,{a}),mul(e,{a},STRONG))
            if nxt not in seen:seen[nxt]=seen[R,e]+(a,);q.append(nxt)
    checks=0;idempotents=set()
    for (R,e),w in seen.items():
        assert R-{'Id'}==e
        if mul(e,e,STRONG)==e:
            E=e|{'Id'}
            assert mul(R,R)==E
            assert E in EQ and E!={'Id'}
            checks+=1;idempotents.add(e)
    assert idempotents=={E-{'Id'} for E in EQ if E!={'Id'}}
    L=frozenset({'p'})
    for e,f in product(idempotents,repeat=2):
        meet=e&f;join=mul(e,f,STRONG)
        assert meet and meet in idempotents and join in idempotents
        assert e<=join and f<=join
        assert all(not(e<=g and f<=g) or join<=g for g in idempotents)
        assert mul(L,e,STRONG)==e==mul(e,L,STRONG)
    # Primitive free two-colour table: least idempotent is not a unit on atoms.
    free={'edge','nonedge'};edges=set();vertices=[]
    for i,bits in enumerate(product((0,1),repeat=3)):
        tri=list(range(3*i,3*i+3));vertices.extend(tri)
        for e,bit in zip(combinations(tri,2),bits):
            if bit:edges.add(frozenset(e))
    def fc(x,y):return 'edge' if frozenset((x,y)) in edges else 'nonedge'
    ft={(a,b):set() for a,b in product(free,repeat=2)}
    for x,y,z in product(vertices,repeat=3):
        if len({x,y,z})==3:ft[fc(x,y),fc(y,z)].add(fc(x,z))
    assert all(v==free for v in ft.values())
    assert set().union(*(ft[a,'edge'] for a in free))==free!={'edge'}
    return len(seen),checks,len(idempotents)

def corrected_saturation_visibility():
    J=frozenset({'Id','p','r'});D=J-{'Id'};H_b=frozenset({'Id'});H_c=J
    assert mul(mul(H_b,D),H_c)==J!=D
    assert mul(mul(H_b,D),H_c)-{'Id'}==D
    checked=0;fresh=0
    for H,K,Dhat in product(EQ,EQ,subsets(ALL)):
        if not Dhat or mul(mul(H,Dhat),K)!=Dhat:continue
        D=Dhat-{'Id'}
        if not D:continue
        assert mul(mul(H,D),K)-{'Id'}==D
        for P in subsets(PALETTE):
            if not D<=P:continue
            for J in EQ:
                if not mul(P,P)<=J:continue
                JP=mul(mul(P,J),P)
                assert H<=J and K<=JP
                # Genuine fresh intermediate points repair the guarded proof.
                for x,xp in product(X,repeat=2):
                    if atom(x,xp) not in H:continue
                    ys=[y for y in X if y not in {x,xp} and atom(x,y) in D]
                    assert ys
                    y=ys[0];assert atom(xp,y) in D and atom(xp,y) in P
                    fresh+=1
                checked+=1
    return checked,fresh

def literal_seams():
    checked=0
    for n in range(1,7):
        for start in range(5):
            for moves in product(range(3),repeat=n):
                values=[start]
                for d in moves:values.append((values[-1]+d)%5)
                composite=(start+sum(moves))%5
                assert composite==values[-1]
                checked+=1
    # Two distinct orphan free factors may collapse under HE. The resulting
    # common target value is not literal source equality and cannot be a seam.
    source=['q','qprime'];h={s:'target' for s in source}
    assert source[0]!=source[1] and h[source[0]]==h[source[1]]
    # Total unary one-/two-root supports distinguish an actual endpoint join
    # from a relation among descendants on an unjoined real ancestor pair.
    U={'x':{'x','u'},'y':{'y','v'},'u':{'u'},'v':{'v'}}
    left={'x','u','v'};right={'y','u','v'}
    assert left&right=={'u','v'} and left|right==set(U)
    assert all(U[z]<=side for side in [left,right] for z in side)
    assert {'u','v'}<=left and not {'x','y'}<=left and not {'x','y'}<=right
    return checked

def private_insertion_bookkeeping():
    # Actual independent-coordinate clone window, preserving shared pinned
    # roots and realizing the EXACT listed atom words on distinct positions.
    roots=[(0,0,0),(0,0,1),(0,1,0),(1,0,0),(1,1,0)]
    base=set(roots);current=set(base);interiors=[]
    obligations=[(0,1,('p','p','p','p')),(1,2,('p','r','p')),
                 (0,1,('p',)),(0,4,('p','r','c','p','p','p')),
                 (3,4,('r','p'))]
    candidates=list(product(range(3),range(3),range(2,24)))
    base_pairs={(x,y):atom(x,y) for x,y in product(base,repeat=2)}
    for i,j,word in obligations:
        p,q=roots[i],roots[j]
        assert p!=q and {p,q}<=base
        def find(path,remaining):
            if len(remaining)==1:
                return path+[q] if atom(path[-1],q)==remaining[0] else None
            for z in candidates:
                if z in current or z in path or atom(path[-1],z)!=remaining[0]:continue
                out=find(path+[z],remaining[1:])
                if out is not None:return out
            return None
        path=find([p],word);assert path is not None
        assert len(path)==len(set(path))
        assert tuple(atom(x,y) for x,y in zip(path,path[1:]))==word
        new=set(path[1:-1]);assert new.isdisjoint(current)
        current|=new;interiors.append(new)
        assert all(atom(x,y)==c for (x,y),c in base_pairs.items())
    assert all(A.isdisjoint(B) for A,B in combinations(interiors,2))
    assert atom(X[0],X[0])=='Id' and 'Id' not in PALETTE
    return len(obligations),sum(map(len,interiors))

if __name__=='__main__':
    w,e,l=word_envelopes();v,f=corrected_saturation_visibility();t=literal_seams();i,n=private_insertion_bookkeeping()
    print(f'PASS B057: {w} RAW/STRONG states/{e} exact word-square checks/{l} idempotents; {v} corrected branch cases/{f} fresh witnesses; {t} literal telescopes; {i} private insertions/{n} interiors. Printed TV1 counterexample retained; bounded diagnostics only.')
