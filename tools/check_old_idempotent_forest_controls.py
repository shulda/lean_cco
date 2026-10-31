#!/usr/bin/env python3
"""Bounded B058 diagnostics; no proof of arbitrary forest height or CCO/SAP."""
from functools import lru_cache
from itertools import product,combinations

@lru_cache(None)
def compositions(n,k):
    if k==1:return ((n,),) if n>=1 else ()
    return tuple((a,)+z for a in range(1,n-k+2) for z in compositions(n-a,k-1))

@lru_cache(None)
def shapes(n):
    if n==1:return ((),)
    out=[]
    for k in range(2,n+1):
        for ns in compositions(n,k):
            out.extend(product(*(shapes(v) for v in ns)))
    return tuple(out)

def node(shape,labels,pos=0):
    if not shape:return dict(lo=pos,hi=pos+1,value=labels[pos],children=[],height=0),pos+1
    children=[]
    for sh in shape:
        z,pos=node(sh,labels,pos);children.append(z)
    return dict(lo=children[0]['lo'],hi=children[-1]['hi'],value=max(z['value'] for z in children),children=children,height=1+max(z['height'] for z in children)),pos

def valid(z):
    ch=z['children']
    return all(valid(c) for c in ch) and (len(ch)<3 or len({c['value'] for c in ch})==1)

def prune(z):
    ch=z['children']
    if not ch:return [('leaf',z['lo'],z['hi'],z['value'])]
    if len(ch)==2:return prune(ch[0])+prune(ch[1])
    assert len({c['value'] for c in ch})==1
    # STOP on the entire original middle. Never enumerate its descendants.
    return prune(ch[0])+[('gap',ch[0]['hi'],ch[-1]['lo'],ch[0]['value'])]+prune(ch[-1])

def all_deletions_bad(z):
    ch=z['children'];out=[]
    if len(ch)>=3:out.append((ch[0]['hi'],ch[-1]['lo']))
    for c in ch:out+=all_deletions_bad(c)
    return out

def tree_controls():
    tests=0;wide=0;maxgap=0
    for n in range(1,8):
        assignments={(1,)*n,(2,)*n,tuple(1+(i%2) for i in range(n)),tuple(1+(i==n//2) for i in range(n))}
        for sh in shapes(n):
            for lab in assignments:
                z,end=node(sh,lab);assert end==n
                if not valid(z):continue
                rec=prune(z);cursor=0;covered=[];leafs=[];boundaries=[]
                for typ,lo,hi,value in rec:
                    assert lo==cursor and lo<hi;cursor=hi;covered.extend(range(lo,hi))
                    assert max(lab[lo:hi])==value
                    if typ=='leaf':assert hi==lo+1;leafs.append(lo)
                    else:wide+=1;boundaries.extend((lo,hi));maxgap=max(maxgap,hi-lo)
                assert covered==list(range(n)) and cursor==n
                roots={x for i in leafs for x in (i,i+1)}
                assert set(boundaries)<=roots and {0,n}<=roots
                assert len(leafs)<=2**z['height']
                assert len(roots)<=2*len(leafs)<=2**(z['height']+1)
                # Each ORIGINAL word is distinguishable, even at equal value.
                words=[tuple((i,j,lab[i]) for j in range(1+(i%3))) for i in range(n)]
                rebuilt=tuple(x for typ,lo,hi,value in rec for w in words[lo:hi] for x in w)
                assert rebuilt==tuple(x for w in words for x in w)
                tests+=1
    # A wide ancestor with a wide discarded child exposes nested-record error.
    sh=((),((),(),()),())
    z,_=node(sh,(1,)*5);bad=all_deletions_bad(z)
    assert len(bad)==2 and bad[0][0]<=bad[1][0]<bad[1][1]<=bad[0][1]
    good=prune(z);assert [r[1:3] for r in good if r[0]=='gap']==[(1,4)]
    # Three first/last retained pairs can have four roots, exceeding L+1.
    roots={0,1,4,5};assert len(roots)==4>2+1
    return tests,wide,maxgap

def typed_nonzero_controls():
    zero=None;S=[zero]+list(product(range(2),repeat=2))
    def mul(x,y):
        if x is None or y is None or x[1]!=y[0]:return None
        return x[0],y[1]
    count=0
    for a,b,c in product(S,repeat=3):
        assert mul(mul(a,b),c)==mul(a,mul(b,c));count+=1
    words=0
    for n in range(1,9):
        for sorts in product(range(2),repeat=n+1):
            letters=list(zip(sorts,sorts[1:]));v=letters[0]
            for x in letters[1:]:v=mul(v,x);assert v is not None
            for lo in range(n):
                p=letters[lo]
                for hi in range(lo+1,n):p=mul(p,letters[hi]);assert p is not None
            words+=1
    assert mul((0,1),(0,1)) is None
    return count,words

def old_term_controls():
    # Explicit canonical quotient coordinates using potentials on three sorts.
    # Each transition is a pointwise named map, not an arbitrary chosen chart.
    q=7;pot=[0,2,5];checks=0
    def trans(a,b,x):return (x-pot[a]+pot[b])%q
    def closure(root_sort,root_value):return {(j,trans(root_sort,j,root_value)) for j in range(3)}
    for length in range(1,7):
        for path in product(range(3),repeat=length+1):
            if path[-1]!=path[0]:continue
            for x in range(q):
                vals=[x]
                for a,b in zip(path,path[1:]):vals.append(trans(a,b,vals[-1]))
                assert vals[-1]==vals[0]
                # Both boundary term vertices survive deletion of all middle
                # root positions in the literal union of boundary closures.
                B=closure(path[0],vals[0])|closure(path[-1],vals[-1])
                assert (path[0],vals[0]) in B and (path[-1],vals[-1]) in B
                assert closure(path[0],vals[0])==closure(path[-1],vals[-1])
                checks+=1
    # Unequal OLD seam values cannot be substituted just because a target map
    # collapses their two vertices. The source indices remain different.
    old=('q',0);other=('q',1);h={old:0,other:0}
    assert old!=other and h[old]==h[other]
    return checks

def cycle_assembly_controls():
    tests=0
    for n in range(3,15):
        # Alternate retained original letters and maximal gap words. Their
        # disjoint interval list partitions the complementary path exactly.
        cuts=[0]+list(range(1,n,3))+[n]
        cuts=sorted(set(cuts));segments=list(zip(cuts,cuts[1:]))
        roots={i:('old',i) for pair in segments for i in pair}
        original=[('a',i,j) for i in range(n) for j in range(1+(i%3))]
        bymacro=[[('a',i,j) for j in range(1+(i%3))] for i in range(n)]
        traversals=[];used=set(roots.values());serial=0
        for lo,hi in segments:
            word=[a for w in bymacro[lo:hi] for a in w]
            pts=[roots[lo]]
            for _ in range(len(word)-1):pts.append(('new',serial));serial+=1
            pts.append(roots[hi]);assert len(set(pts))==len(pts)
            assert set(pts[1:-1]).isdisjoint(used);used.update(pts[1:-1])
            traversals.append((pts,word))
        # Fixed ORIGINAL anchor returns from n to0 with separate new interior.
        anchor=[('anchor',0),('anchor',1)];anchor_pts=[roots[n],('anchor_new',0),roots[0]]
        assert set(anchor_pts[1:-1]).isdisjoint(used)
        cycle=[];labels=[]
        for pts,w in traversals+[(anchor_pts,anchor)]:cycle+=pts[:-1];labels+=w
        assert len(cycle)==len(set(cycle)) and len(labels)==len(cycle)
        assert labels==original+anchor
        # Distinct root names are needed before E=Id union e implies e.
        E=lambda x,y:x[0]==y[0]
        x=(0,0);same=(0,0);fresh=(0,1)
        assert E(x,same) and x==same and E(x,fresh) and x!=fresh
        # Complement admissibility alone does not imply fixed anchor menu.
        retained_profile={'r','s'};anchor_profile={'r'};chosen='s'
        assert chosen in retained_profile and chosen not in anchor_profile
        tests+=1
    return tests

if __name__=='__main__':
    t,w,g=tree_controls();a,p=typed_nonzero_controls();e=old_term_controls();c=cycle_assembly_controls()
    print(f'PASS B058: {t} valid forest cases/{w} maximal gaps/max gap{g}; {a} typed associativity triples/{p} composable paths; {e} literal OLD transport cases; {c} exact simple-cycle assemblies. Bounded diagnostics only; external forest theorem remains unbound.')
