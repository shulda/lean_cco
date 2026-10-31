#!/usr/bin/env python3
"""Bounded B055 diagnostics; no infinite SAP, CCO, or Lean certificate."""
from itertools import product,permutations

# Two actual original real sorts, a common block index, independent clones.
BLOCKS=3;CLONES=2
REAL={s:[(s,b,k) for b,k in product(range(BLOCKS),range(CLONES))] for s in (0,1)}
GROUP=[(p,mask) for p in permutations(range(BLOCKS)) for mask in range(1<<(2*BLOCKS))]
def greal(g,x):
    p,m=g;s,b,k=x
    return s,p[b],k^((m>>(s*BLOCKS+b))&1)
def fine(x,y):
    if x==y:return x[0],y[0],'real_Id'
    return x[0],y[0],'same_block' if x[1]==y[1] else 'different_block'

# source, kind, output tag. The extra identity copy exercises the generic
# diagonal-only graph between DIFFERENT output sorts, not logical equality.
DESCS=[(s,kind,tag) for s in (0,1) for kind,tag in [
    ('real','real'+str(s)),('block','Q'+str(s)),
    ('block','Q'+str(1-s)),('real','copy'+str(s))]]
def value(d,x):
    s,kind,tag=d;assert x[0]==s
    return (tag,x[1],x[2]) if kind=='real' else (tag,x[1])
def gout(g,d,v):
    p,m=g;s,kind,tag=d
    return (tag,p[v[1]],v[2]^((m>>(s*BLOCKS+v[1]))&1)) if kind=='real' else (tag,p[v[1]])
def equivalent(d,x,y):return value(d,x)==value(d,y)

def orbital_tests():
    cases=0;parts=0;empty=0;rawchecks=0
    for d,e in product(DESCS,repeat=2):
        X,Y=REAL[d[0]],REAL[e[0]]
        allpairs={(value(d,x),value(e,y)) for x,y in product(X,Y)}
        orbitals=[]
        while allpairs:
            u,v=next(iter(allpairs))
            orb={(gout(g,d,u),gout(g,e,v)) for g in GROUP}
            assert orb<=allpairs
            allpairs-=orb;orbitals.append(orb)
        seen=set();empty_here=0
        for orb in orbitals:
            pull={(x,y) for x,y in product(X,Y) if (value(d,x),value(e,y)) in orb}
            div={(x,y) for x,y in pull if x!=y}
            if not div:
                empty+=1;empty_here+=1
                assert d[0]==e[0] and d[1]==e[1]=='real'
                assert pull=={(x,x) for x in X}
                continue
            parts+=1
            u,v=next(iter(div));t=fine(u,v)
            O={(x,y) for x,y in product(X,Y) if fine(x,y)==t}
            # Compute full kernel saturation BEFORE the real-diversity guard.
            sat={(x,y) for x,y in product(X,Y) if any(
                equivalent(d,x,a) and equivalent(e,b,y) for a,b in O)}
            assert sat==pull
            guard={p for p in sat if p[0]!=p[1]}
            assert guard==div
            palette={fine(x,y) for x,y in div}
            assert not(seen&palette);seen|=palette
            rawchecks+=len(sat);cases+=1
        assert empty_here<=1
        assert seen=={fine(x,y) for x,y in product(X,Y) if x!=y}
    # Hidden quotient equality has a nonempty old diversity pullback.
    qa=(0,'block','Q0');qr=(0,'real','real0')
    assert any(x!=y and value(qa,x)==value(qa,y) for x,y in product(REAL[0],repeat=2))
    assert not any(x!=y and value(qr,x)==value(qr,y) for x,y in product(REAL[0],repeat=2))
    return cases,parts,empty,rawchecks


def completed_hom_tests():
    # A smaller completed real+quotient window; enumerate all sort-preserving
    # maps commuting with the projection, not just known automorphisms.
    R=list(product(range(2),range(3)));Q=range(2)
    def rel(x,y):return ('eq' if x==y else 'same' if x[0]==y[0] else 'different')
    checked=0;hom=0
    for qmap in product(Q,repeat=2):
        choices=[[(qmap[b],k) for k in range(3)] for b,k in R]
        for vals in product(*choices):
            fmap=dict(zip(R,vals));checked+=1
            if any(qmap[a]==qmap[b] for a,b in product(Q,repeat=2) if a!=b):continue
            if any(rel(x,y)!=rel(fmap[x],fmap[y]) for x,y in product(R,repeat=2) if x!=y):continue
            hom+=1
            assert len(set(vals))==len(R)
            # Complete binary partitions reflect all pairs, including diagonal.
            assert all(rel(x,y)==rel(fmap[x],fmap[y]) for x,y in product(R,repeat=2))
            assert all((x[0]==q)==(fmap[x][0]==qmap[q]) for x in R for q in Q)
    assert hom==2*6*6
    return checked,hom


def anchor_clone_tests():
    # Independent row/column MI quotient axes, no cell quotient added.
    R=list(product(range(4),range(4),range(5)))
    def col(x,y):return (x[0]==y[0],x[1]==y[1]) if x!=y else 'Id'
    def terms(x):return {('row',x[0]),('col',x[1])}
    p=(1,2,0);anchors=[(1,0,0),(0,2,0),(3,3,0)]
    others=[(2,1,0),(1,3,0)]
    frame=anchors+others
    candidates=[x for x in R if x!=p and x not in frame and all(col(x,z)==col(p,z) for z in frame)]
    assert candidates
    checks=0
    for pp in candidates:
        assert terms(pp)==terms(p)
        for z in anchors:
            assert (pp[0]==z[0],pp[1]==z[1])==(p[0]==z[0],p[1]==z[1]);checks+=1
    # Repeat cloning with previous clones in the literal complete base.
    positions=[p,p,p];chosen=[]
    while len(set(positions))<len(positions):
        occupied=set(frame)|set(positions)|set(chosen)
        pp=next(x for x in R if x not in occupied and all(col(x,z)==col(p,z) for z in frame+chosen))
        positions[positions.index(p)]=pp;chosen.append(pp)
        assert terms(pp)==terms(p)
    assert len(set(positions))==3
    assert set(positions).isdisjoint(anchors)
    return len(candidates),checks,len(chosen)


def support_tests():
    # Functions x->u,y->v; displayed quotient relation u-v does NOT join roots.
    universe={'x','y','u','v'};f={'x':'u','y':'v','u':'u','v':'v'}
    relation={frozenset({'u','v'})}
    def closed(S):return all(f[x] in S for x in S)
    A={'u','v'};L={'x','u','v'};R={'y','u','v'}
    assert all(closed(S) for S in (A,L,R,universe))
    assert L|R==universe and L&R==A and L<universe and R<universe
    assert all(t<=L or t<=R for t in relation)
    # A DIRECT real tuple x-y prevents this free decomposition and its full
    # closed support is joined. Its two-element tuple alone is not closed.
    direct=frozenset({'x','y'})
    assert not closed(set(direct)) and not(direct<=L or direct<=R)
    # A one-generated functional chain is irreducible because a factor with
    # its generator contains all values, even without binary relations.
    g={'a':'b','b':'c','c':'c'}
    for bits in product((False,True),repeat=3):
        S={v for v,b in zip(g,bits) if b}
        if 'a' in S and all(g[v] in S for v in S):assert S==set(g)
    return 3


def positive_word_window():
    # A full equivalence endpoint with three clones has a length-two RAW p
    # word including its real diagonal. Use fresh intermediate clones to
    # witness the concatenated J ; cross-same-block ; K STRONG word.
    X=[(0,b,k) for b,k in product(range(3),range(4))]
    Y=[(1,b,k) for b,k in product(range(3),range(4))]
    count=0
    for x,y in product(X,Y):
        wanted=x[1]==y[1]
        witness=any(x[1]==a[1]==b[1]==c[1]==d[1]==y[1] and len({x,a,b,c,d,y})==6
                    for a,b in permutations([u for u in X if u[1]==x[1] and u!=x],2)
                    for c,d in permutations([v for v in Y if v[1]==y[1] and v!=y],2))
        assert witness==wanted;count+=1
    return count

if __name__=='__main__':
    c,p,e,r=orbital_tests();m,h=completed_hom_tests();a,k,s=anchor_clone_tests();z=support_tests();w=positive_word_window()
    print(f'PASS B055: {c} saturated orbital cases/{e} real-diagonal exceptions/{r} RAW pairs; {m} completed maps/{h} embeddings; {a} anchored clones/{k} readings/{s} collision splits; {z} source-support guards; {w} positive word pairs. Bounded diagnostics only.')
