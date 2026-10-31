#!/usr/bin/env python3
"""Bounded B051 old profile diagnostics, not unbounded SAP/CCO certification."""
from collections import Counter
from itertools import product
import json,signal,time
START=time.monotonic();C=Counter()
def demand(p,m):
    if not p:raise AssertionError(m)
def mat(n,p):return tuple(sum(1<<y for y in range(n) if p(x,y)) for x in range(n))
def union(*rs):return tuple(a|b for a,b in zip(rs[0],union(*rs[1:]))) if len(rs)>1 else rs[0]
def comp(r,s):
    out=[]
    for row in r:
        value=0
        for y in range(len(r)):
            if row>>y&1:value|=s[y]
        out.append(value)
    return tuple(out)
def circ(r):return tuple(v&~(1<<x) for x,v in enumerate(r))
def strong(r,s):return circ(comp(r,s))
def subset(r,s):return all(not(a&~b) for a,b in zip(r,s))
def meet(r,s):return tuple(a&b for a,b in zip(r,s))
def path(r,n,x,z):
    def go(v,k,used):
        if k==0:return v==z
        candidates=r[v]&~used
        if k==1:return bool(candidates>>z&1)
        candidates&=~(1<<z)
        while candidates:
            bit=candidates&-candidates;candidates-=bit;y=bit.bit_length()-1
            if go(y,k-1,used|bit):return True
        return False
    return go(x,n,1<<x)

def reproduction_and_powers():
    # Three old equivalence blocks, each with six clone points. This window
    # is ample only for the path lengths <=5 explicitly checked below.
    width=6;n=3*width
    j=mat(n,lambda x,y:x//width==y//width);clone=circ(j)
    far=mat(n,lambda x,y:x//width!=y//width);top=union(clone,far)
    menus=[clone,far,top]
    for e,cs in [(clone,[clone]),(top,menus)]:
        for c in cs:
            demand(strong(e,c)==e==strong(c,e),'nonzero equivalence reproduction')
            C['equivalence_reproduction_cases']+=1
        demand(strong(e,e)==e,'equivalence idempotence')
    for jdiv in [clone,top]:
        for p,q in product(menus,repeat=2):
            if subset(strong(p,q),jdiv):
                demand(subset(p,jdiv) and subset(q,jdiv),'terminal no-return finite-window check')
                C['local_no_return_implications']+=1
            # Saturation includes P even when P is outside J: RAW reflexivity.
            fullj=union(jdiv,mat(n,lambda x,y:x==y))
            phat=strong(strong(jdiv,p),jdiv)
            demand(subset(p,phat),'RAW saturation must contain arbitrary P')
            demand(phat==circ(comp(comp(fullj,p),fullj)),'RAW/STRONG saturation differs')
            C['arbitrary_menu_saturation_inclusions']+=1
    for w in menus:
        expected=clone if w==clone else top
        threshold=2 if w==far else 1
        power=w
        for length in range(1,6):
            if length>=threshold:demand(power==expected,'eventual profile menu not stabilized')
            for z in range(1,n):
                demand(bool(power[0]>>z&1)==path(w,length,0,z),'whole distinct path differs from recursive menu')
                C['independent_distinct_profile_paths']+=1
            C['bounded_profile_powers']+=1
            power=strong(power,w)
        demand(strong(expected,expected)==expected,'connectedness palette idempotence')
    # At the nonzero represented cut J, the external layer itself is one
    # old atom in this diagnostic model. No general layer theorem certified.
    demand(far==circ(mat(n,lambda x,y:x//width!=y//width)),'positive external layer witness')
    C['single_word_cover_layer_witnesses']+=1


def cylinder_boundaries():
    width=3;n=4*width
    rs=[mat(n,lambda x,y,g=g:x!=y and (x//width)^(y//width)==g) for g in range(4)]
    j=mat(n,lambda x,y:x//width==y//width);jd=circ(j)
    demand(rs[0]==jd,'quotient diagonal must pull back to nonempty clone diversity')
    for i,k in product(range(1,4),repeat=2):
        result=strong(rs[i],rs[k]);returns=any(meet(result,jd))
        demand(returns==(i==k),'exact COMPLETE cylinder return failed')
        demand(result==(jd if i==k else rs[i^k]),'actual V4 product table')
        C['complete_cylinder_return_pairs']+=1
    # Infinite-clone counterpart is homogeneous SAP but has a quotient
    # index-two interval: it is deliberately NOT terminal.
    p=rs[1];demand(strong(p,p)==jd and not subset(p,jd),'index-two no-return obstruction')
    h=union(j,p)
    for x in range(n):
        owner_classes={y//width for y in range(n) if h[x]>>y&1}
        demand(len(owner_classes)==2,'involution must give index two above J')
        C['actual_index_two_class_counts']+=1
    C['no_return_requires_NR2_guard']+=1
    t,s=union(rs[1],rs[2]),union(rs[2],rs[3])
    demand(t!=s and any(meet(strong(t,s),jd)),'incomplete union boundary missing')
    C['incomplete_cylinder_union_guard']+=1
    # J=Id cannot provide Phi(Delta) diversity or the fresh same-class point.
    identity=mat(n,lambda x,y:x==y)
    demand(not any(circ(identity)) and any(jd),'zero-cut diversity diagonal distinction')
    C['nonzero_J_and_diagonal_guard']+=1
    # Each index-two full cover has a one-atom external layer here.
    for i in range(1,4):
        layer=rs[i];demand(any(layer) and not any(meet(layer,j)),'external single-word layer')
        C['single_word_cover_layer_witnesses']+=1


def main():
    reproduction_and_powers();cylinder_boundaries()
    print(json.dumps(dict(status='PASS',seconds=round(time.monotonic()-START,3),counts=dict(sorted(C.items())),
        limits='Finite clone windows for bounded original paths/products only. No finite host has claimed unbounded SAP/CCO, arbitrary long STRONG paths, general NR2, the cover-layer theorem, hidden SAP or Lean certification.'),sort_keys=True))
if __name__=='__main__':signal.alarm(30);main()
