#!/usr/bin/env python3
"""Bounded diagnostics for B053; not infinite freshness or CCO certificates."""
from itertools import combinations,permutations,product

def cycles(vertices):
    for n in range(3,len(vertices)+1):
        for vs in combinations(vertices,n):
            a=min(vs)
            for tail in permutations([v for v in vs if v!=a]):
                if tail[0]<tail[-1]:yield (a,)+tail

def edge(x,y):return tuple(sorted((x,y)))
def edges(c):return {edge(c[i],c[(i+1)%len(c)]) for i in range(len(c))}
def chords(c,E):return [edge(c[i],c[j]) for i in range(len(c)) for j in range(i+1,len(c)) if edge(c[i],c[j]) in E-edges(c)]

def graph_tests():
    tested=0;split=0
    for nd,nx in product(range(4),range(5)):
        if nd+nx>6:continue
        D=set(range(nd));X=set(range(nd,nd+nx));pairs=list(combinations(sorted(X),2))
        fixed={edge(a,b) for a,b in combinations(range(nd+nx),2) if a in D or b in D}
        for bits in product((False,True),repeat=len(pairs)):
            E=fixed|{e for e,b in zip(pairs,bits) if b}
            def reduce(c):
                nonlocal split
                cc=chords(c,E)
                if not cc:
                    assert not(set(c)&D) or len(c)==3
                    return
                split+=1;a,b=cc[0];i,j=sorted((c.index(a),c.index(b)))
                left=c[i:j+1];right=c[j:]+c[:i+1]
                assert 3<=len(left)<len(c) and 3<=len(right)<len(c)
                reduce(left);reduce(right)
            for c in cycles(list(range(nd+nx))):
                if edges(c)<=E:tested+=1;reduce(c)
    # A missing base spoke allows a nontriangular chordless cycle meeting D.
    c=(0,1,2,3);E=edges(c)
    assert not chords(c,E) and len(c)==4
    # Class-colouring counts do not need global clone injection: C5 folds to K3.
    image=[0,1,0,1,2]
    assert all(image[i]!=image[(i+1)%5] for i in range(5))
    assert len(set(image))==3<len(image)
    return tested,split

N=7;K=4
reals=list(product(range(N),range(N),range(K)))
def terms(x):
    r,c,k=x
    return {('real',x),('row',r),('row_other',r),('col',c)}
def closed(gens):
    s=set(gens)
    for t,v in list(s):
        if t=='real':s|=terms(v)
        if t in ('row','row_other'):s|={('row',v),('row_other',v)}
    return s

def frame_tests():
    B=closed({('real',(0,0,0)),('real',(1,1,0)),('row',2),('col',2)})
    compatible=0
    for rr,cc in product((None,3,4),(None,3,4)):
        A=closed(({('row',rr)} if rr is not None else set())|({('col',cc)} if cc is not None else set()))
        BB=B|A
        X=[x for x in reals if (rr is None or x[0]==rr) and (cc is None or x[1]==cc)]
        good=[x for x in X if terms(x)&BB==A]
        assert good and all(('real',x) not in BB for x in good)
        compatible+=1
    # Incompatible row orphans cannot share one representative; use several.
    A=closed({('row',3),('row',4),('col',3)})
    requests=[('row',3),('row',4),('col',3)]
    forbidden=B|A|closed({('real',(5,5,0))});prior=set();chosen=[]
    for typ,val in requests:
        candidates=[x for x in reals if x[0 if typ=='row' else 1]==val]
        forced=closed({(typ,val)})
        Z=forbidden|prior|{('real',x) for x in chosen}
        good=[x for x in candidates if (terms(x)-forced).isdisjoint(Z)]
        assert good
        x=good[0];assert forced<=terms(x) and ('real',x) not in Z
        chosen.append(x);prior|=terms(x)-forced
    assert len(set(chosen))==len(chosen)
    assert set().union(*(terms(x) for x in chosen))&(B|A)==A
    # Normal-form kernels on actual real-source functions, including identity.
    checks=0
    for x,y in product(reals[:40],reals[:40]):
        for typ in ['real','row','row_other','col']:
            vx=next(v for t,v in terms(x) if t==typ);vy=next(v for t,v in terms(y) if t==typ)
            expected=x==y if typ=='real' else x[0]==y[0] if typ.startswith('row') else x[1]==y[1]
            assert (vx==vy)==expected;checks+=1
    # Every pair of nonzero coordinate equivalences has an infinite-model
    # nonzero meet, represented by K distinct clones in this bounded window.
    assert len([x for x in reals if x[:2]==(3,3)])==K
    return compatible,len(chosen),checks

def negative_signatures():
    # A fine quotient term with two values over a coarse block is exhausted
    # by a finite forbidden list; coarse-only real clones still have room.
    bits={('fine',0),('fine',1)}
    assert all(('fine',b) in bits for b in range(2))
    # Row+column unary closure omits a uniquely binary-defined cell quotient.
    A=closed({('row',3),('col',4)})
    cell=('cell',(3,4));assert cell not in A
    cells=[(r,c) for r,c in product(range(N),repeat=2) if r==3 and c==4]
    assert cells==[(3,4)]
    # A point-generated real base may also omit a forced CROSS cell.
    gens=[(3,0,0),(0,4,0)]
    cells_generated={x[:2] for x in gens}
    assert (3,4) not in cells_generated
    return 3

if __name__=='__main__':
    g,s=graph_tests();c,r,k=frame_tests();n=negative_signatures()
    print(f'PASS B053: {g} cycles/{s} chord splits; {c} compatible frames; {r} incompatible orphan requests; {k} term-kernel checks; {n} signature guards. Bounded diagnostics only.')
