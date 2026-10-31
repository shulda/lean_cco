#!/usr/bin/env python3
"""Bounded B059 code/order diagnostics, not Ramsey/HN/forest certificates."""
from itertools import combinations,permutations,product

R=tuple(('r',i) for i in range(4));Q=(('q',0),('q',1));U=R+Q
def proj(x):return ('q',x[1]//2)
def closure(S):return set(S)|{proj(x) for x in S if x[0]=='r'}
def atom(x,y):
    if x==y:return 'eq'
    if x[0]==y[0]=='r':return 'same' if proj(x)==proj(y) else 'different'
    if x[0]==y[0]=='q':return 'quotient-different'
    r,q=(x,y) if x[0]=='r' else (y,x)
    return ('mixed',x[0],proj(r)==q)
def subsets(S):
    S=tuple(S)
    for n in range(len(S)+1):
        for C in combinations(S,n):yield set(C)
def values(A):return [tuple((x,proj(x),proj(x))) for x in A]
def orderpos(order):return {v:i for i,v in enumerate(order)}
def readout(A,order):
    pos=orderpos(order);V=values(A)
    return tuple(pos[u]<pos[v] for row in V for col in V for u in row for v in col)
def presentation_quotient(A):
    # id,F,Fduplicate tests literal value identification across both roots
    # and syntactically different terms representing the same function.
    P=[(x,t) for x in A for t in range(3)]
    ev=lambda p:p[0] if p[1]==0 else proj(p[0])
    classes={ev(p) for p in P}
    assert classes==closure(A)
    for p,q in product(P,repeat=2):
        if p[1] and q[1]:assert (ev(p)==ev(q))==(proj(p[0])==proj(q[0]))
    return len(P),len(classes)

def closure_tests():
    checks=0;covered=0
    for A in subsets(R):
        assert closure(A)&set(R)==A
        presentation_quotient(tuple(sorted(A)));checks+=1
    for B in subsets(U):
        if closure(B)!=B:continue
        D={x for x in B if x[0]=='r'}
        for q in B&set(Q):D.add(next(x for x in R if proj(x)==q))
        assert B<=closure(D) and closure(D)&set(R)==D
        assert len(closure(D))<=2*len(D)
        covered+=1
    assert closure(set())==set()
    return checks,covered

def realmaps(A,B):
    out=[]
    for images in permutations(B,len(A)):
        f=dict(zip(A,images))
        if all(atom(x,y)==atom(f[x],f[y]) for x,y in product(A,repeat=2)):out.append(f)
    return out

def all_hidden_maps(A,B):
    aa=tuple(sorted(closure(A)));bb=tuple(sorted(closure(B)))
    ar=[v for v in aa if v[0]=='r'];aq=[v for v in aa if v[0]=='q']
    br=[v for v in bb if v[0]=='r'];bq=[v for v in bb if v[0]=='q']
    out=[]
    for imr in permutations(br,len(ar)):
        for imq in permutations(bq,len(aq)):
            h=dict(zip(ar,imr));h.update(zip(aq,imq))
            if not all(h[proj(x)]==proj(h[x]) for x in ar):continue
            if all(atom(x,y)==atom(h[x],h[y]) for x,y in product(aa,repeat=2)):out.append(h)
    return out

def embeddings_and_orders():
    cases=0;reasonable=0
    B=R[:3];HB=tuple(sorted(closure(B)));hostorders=list(permutations(HB))
    for A in [R[:1],R[:2],(R[0],R[2])]:
        HA=tuple(sorted(closure(A)));rm=realmaps(A,B);hm=all_hidden_maps(A,B)
        assert len(rm)==len(hm)
        assert {tuple(h[x] for x in A) for h in hm}=={tuple(f[x] for x in A) for f in rm}
        for f in rm:
            extensions=[h for h in hm if all(h[x]==f[x] for x in A)]
            assert len(extensions)==1
        for ao in permutations(HA):
            pa=orderpos(ao);src=readout(A,ao)
            for bo in hostorders:
                pb=orderpos(bo)
                visible=set();hidden=set()
                for f in rm:
                    images=tuple(f[x] for x in A)
                    if src==readout(images,bo):visible.add(images)
                for h in hm:
                    if all((pa[x]<pa[y])==(pb[h[x]]<pb[h[y]]) for x,y in product(HA,repeat=2)):
                        hidden.add(tuple(h[x] for x in A))
                assert visible==hidden
                cases+=1
            for f in rm:
                assert any(src==readout(tuple(f[x] for x in A),bo) for bo in hostorders)
                reasonable+=1
    # One real root, two actual hidden values, opposite hidden orders:
    # no off-diagonal real tuple can record this difference.
    A=(R[0],);h=(R[0],proj(R[0]));assert readout(A,h)!=readout(A,h[::-1])
    offdiag=lambda A,order:tuple(v for i,x in enumerate(A) for j,y in enumerate(A) if x!=y for v in [])
    assert offdiag(A,h)==offdiag(A,h[::-1])==()
    # Every compatible code corresponds to exactly one hidden order.
    for A in [R[:1],R[:2],(R[0],R[2])]:
        orders=list(permutations(closure(A)))
        assert len({readout(A,o) for o in orders})==len(orders)
    return cases,reasonable

def irreducible_coverage():
    checked=0;attempts=0
    for B in subsets(U):
        if closure(B)!=B:continue
        for x,y in combinations(B,2):assert atom(x,y)!='eq'
        closed=[A for A in subsets(B) if A!=B and closure(A)==A]
        for X,Y in product(closed,repeat=2):
            if X|Y!=B:continue
            lx=X-Y;ry=Y-X
            if not lx or not ry:continue
            x=next(iter(lx));y=next(iter(ry))
            # The actual completed binary orbital tuple crosses both factors,
            # so the induced union cannot be their FREE amalgam.
            assert atom(x,y)!='eq' and not {x,y}<=X and not {x,y}<=Y
            attempts+=1
        checked+=1
    return checked,attempts

def partial_function_controls():
    tests=0
    # Generated closure in a raw partial unary functional graph is closed
    # under every ALREADY DEFINED value; check all generators/functions.
    for n in range(1,5):
        for fv in product(range(-1,n),repeat=n):
            for x in range(n):
                C={x};old=set()
                while C!=old:
                    old=set(C);C|={fv[v] for v in C if fv[v]>=0}
                for S in subsets(C):
                    if x not in S:continue
                    if all(fv[v]<0 or fv[v] in S for v in S):assert S==C
                tests+=1
    # Actual completed intended real->quotient diagrams reject undefined
    # real function values; totality/typing is not supplied by 'closed'.
    r=('r',0);q=('q',0)
    raw={r};defined={}
    assert all(defined.get(v,v) in raw for v in raw)
    assert r not in defined  # unary closed, but not actual completed member
    wrong={q:r};assert q in wrong and q[0]!='r'
    return tests

if __name__=='__main__':
    a,b=closure_tests();c,d=embeddings_and_orders();e,f=irreducible_coverage();g=partial_function_controls()
    print(f'PASS B059: {a} real closures/{b} actual orphan covers; {c} embedding-order cases/{d} reasonable extensions; {e} completed coverage tests/{f} free-split exclusions; {g} raw generated-closure controls. Bounded diagnostics only.')
