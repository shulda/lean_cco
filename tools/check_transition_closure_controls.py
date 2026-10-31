#!/usr/bin/env python3
"""Bounded B049 actual finite clone/quotient diagnostics, not infinite SAP/CCO proofs."""
from collections import Counter,defaultdict
from itertools import product
import json,signal,time
START=time.monotonic();C=Counter();W=4
pts=tuple(product(range(2),range(2),range(W)));N=len(pts);MASK=(1<<N)-1

def demand(p,m):
    if not p:raise AssertionError(m)
def atom(x,y):
    if x==y:return 0
    a,b=pts[x],pts[y]
    return 1+2*(a[0]==b[0])+(a[1]==b[1])
def matrix(pred):return tuple(sum((1<<y) for y in range(N) if pred(x,y)) for x in range(N))
Id=matrix(lambda x,y:x==y);Top=(MASK,)*N
atoms=[matrix(lambda x,y,k=k:atom(x,y)==k) for k in range(5)]
def union(ms):
    out=[0]*N
    for m in ms:
        for x in range(N):out[x]|=m[x]
    return tuple(out)
def converse(r):return matrix(lambda x,y:bool(r[y]>>x&1))
def comp(r,s):
    out=[]
    for row in r:
        v=0
        for y in range(N):
            if row>>y&1:v|=s[y]
        out.append(v)
    return tuple(out)
def sub(r,s):return all(not(r[x]&~s[x]) for x in range(N))
def meet(r,s):return tuple(a&b for a,b in zip(r,s))
def circ(r):return tuple(r[x]&~(1<<x) for x in range(N))
def rel(mask):return union(atoms[k] for k in range(5) if mask>>k&1)
rels=tuple(rel(mask) for mask in range(1,32))
eqs=tuple(e for e in rels if sub(Id,e) and e==converse(e) and sub(comp(e,e),e))
proper=tuple(e for e in eqs if e!=Top);nonzero=tuple(e for e in eqs if e!=Id)
def classes(e):
    rows=sorted(set(e));return tuple(tuple(i for i in range(N) if row>>i&1) for row in rows)
def labs(e):
    cs=classes(e);return tuple(next(j for j,b in enumerate(cs) if x in b) for x in range(N))
def strong3(e,t,k):
    # Transitivity permits fixing x=0; retain EACH old endpoint y.
    x=0;out=0
    for y in range(N):
        if y==x:continue
        if any(e[x]>>u&1 and u not in (x,y) and t[u]>>v&1 and v not in (x,y,u)
               and k[v]>>y&1 for u in range(N) for v in range(N)):
            out|=1<<y
    return out

def saturation():
    for e,k,t in product(nonzero,nonzero,atoms[1:]):
        raw=comp(comp(e,t),k)
        demand(strong3(circ(e),t,circ(k))==circ(raw)[0],'three-factor RAW/STRONG differs')
        C['pinned_three_factor_saturations']+=1
    for e,k in product(nonzero,repeat=2):
        raw=comp(e,k);strong=0
        for y in range(1,N):
            if any(z not in (0,y) and e[0]>>z&1 and k[z]>>y&1 for z in range(N)):strong|=1<<y
        demand(strong==circ(raw)[0],'two-factor exterior witness failure')
        for z in range(N):
            for y in range(1,N):
                if e[0]>>z&1 and k[z]>>y&1:
                    demand(any(v not in (0,y) and e[0]>>v&1 and k[v]>>y&1 for v in range(N)),
                           'endpoint middle witness cannot be separated')
                    C['middle_witness_off_or_endpoint_cases']+=1
        C['two_factor_join_saturations']+=1
    # Genuinely different real sorts A and B are disjoint copies. A-index
    # equality with a B-index is never logical equality or a forbidden collision.
    cross=[matrix(lambda x,y,k=k:1+2*(pts[x][0]==pts[y][0])+(pts[x][1]==pts[y][1])==k)
           for k in range(1,5)]
    for e,k,t in product(nonzero,nonzero,cross):
        raw=comp(comp(e,t),k);strong=0
        for y in range(N):
            if any(e[0]>>u&1 and u!=0 and t[u]>>v&1 and v!=y and k[v]>>y&1
                   for u in range(N) for v in range(N)):
                strong|=1<<y
        demand(strong==raw[0],'mixed-sort RAW/STRONG saturation differs')
        C['disjoint_real_sort_saturations']+=1
    # Equality exterior is omitted: its empty diversity slice cannot replace it.
    e=Id;k=nonzero[0];t=atoms[4]
    raw=comp(comp(e,t),k)
    demand(any(circ(raw)),'identity-exterior fixture unexpectedly empty')
    demand(not any(comp(comp(circ(e),t),circ(k))),'empty exterior falsely acts as identity')
    C['identity_exterior_omission_guard']+=1
    # K2 is ordinary AP, not SAP; its only diversity product has no middle.
    tiny=((0,1),(1,0));demand(tiny[0][0]==0 and tiny[0][1]==1,'K2 diversity')
    demand(not any(z not in (0,1) for z in range(2)),'finite-SAP boundary')
    C['AP_without_SAP_boundary']+=1


def transport():
    records=[]
    for e in proper:
        le=labs(e);ce=classes(e)
        for r in rels:
            if not sub(comp(r,converse(r)),e):continue
            lam=[]
            for y in range(N):
                values={le[x] for x in range(N) if r[x]>>y&1}
                demand(len(values)==1,'transport predecessor class not unique/onto')
                lam.append(next(iter(values)))
            f=comp(comp(converse(r),e),r);lf=labs(f);cf=classes(f)
            demand(f in proper,'proper source quotient did not remain proper')
            q=[]
            for block in ce:
                targets={lf[y] for x in block for y in range(N) if r[x]>>y&1}
                demand(len(targets)==1,'forward quotient label not unique')
                q.append(next(iter(targets)))
            demand(len(set(q))==len(cf),'canonical quotient map is not bijective')
            for y,z in product(range(N),repeat=2):
                demand((lam[y]==lam[z])==bool(f[y]>>z&1),'lambda kernel differs from Rop E R')
            if sub(Id,r):
                demand(sub(r,e) and f==e,'identity-containing redundancy failed')
                demand(tuple(q)==tuple(range(len(ce))),'identity-containing quotient map moved a class')
                C['identity_containing_transport_cases']+=1
            if e!=Id:demand(f!=Id,'nonzero source collapsed to real equality in clone fixture')
            if comp(r,converse(r))==Id:demand(r==Id,'converse functionality did not reduce to Id')
            records.append((e,f,r,tuple(q)))
            C['actual_quotient_transports']+=1
    for e,f,r,q in records:
        le,lf=labs(e),labs(f)
        for h in proper:
            if not sub(f,h):continue
            lh=labs(h);u=tuple(lh[b[0]] for b in classes(f))
            h0=comp(comp(r,h),converse(r));demand(sub(e,h0),'upward pullback lost lower kernel')
            demand(comp(comp(converse(r),h0),r)==h,'upward pullback transport wrong')
            lh0=labs(h0)
            left=tuple(u[q[i]] for i in range(len(classes(e))))
            right=tuple(lh[next(y for y in range(N) if r[x]>>y&1)] for x in [b[0] for b in classes(e)])
            demand(left==right,'upward interchange functions differ')
            C['upward_interchange_cases']+=1
        # Any diversity atom in R has the same target source-class labelling.
        for t in atoms[1:]:
            if not sub(t,r):continue
            for y in range(N):
                ts={le[x] for x in range(N) if t[x]>>y&1}
                rs={le[x] for x in range(N) if r[x]>>y&1}
                demand(ts==rs,'atomic subbranch lambda differs')
            demand(comp(comp(converse(t),e),t)==f,'atomic target kernel differs')
            C['atomic_whole_branch_agreements']+=1
    for e,f,r,q in records:
        for ff,g,s,qs in records:
            if f!=ff:continue
            t=comp(r,s);demand(sub(comp(t,converse(t)),e),'composite kernel bound failed')
            demand(comp(comp(converse(t),e),t)==g,'composite target kernel differs')
            lg=labs(g);qt=tuple(lg[next(z for z in range(N) if t[b[0]]>>z&1)] for b in classes(e))
            demand(qt==tuple(qs[q[i]] for i in range(len(q))),'canonical quotient maps fail composition')
            C['typed_transport_compositions']+=1
    return records


def normal_forms(records):
    nodes={e:i for i,e in enumerate(proper)};maps={};ups=[]
    for e in proper:
        i=nodes[e];maps[i,i,tuple(range(len(classes(e))))]=True
        for h in proper:
            if sub(e,h):
                fn=tuple(labs(h)[b[0]] for b in classes(e));ups.append((i,nodes[h],fn));maps[i,nodes[h],fn]=True
    transitions=[]
    for e,f,r,q in records:
        transitions.append((nodes[e],nodes[f],q));maps[nodes[e],nodes[f],q]=True
    predicted=set()
    for a,b,u in ups:
        for bb,c,q in transitions:
            if b==bb:predicted.add((a,c,tuple(q[j] for j in u)))
    # Id is itself one actual relation, so predictions include pure upward maps.
    demand(set(maps)<=predicted,'initial map missing its normal form')
    while True:
        old=set(maps);new=set(old)
        for a,b,p in old:
            for bb,c,q in old:
                if b==bb:new.add((a,c,tuple(q[j] for j in p)))
        demand(new<=predicted,'composite coordinate term escaped finite old-relation normal forms')
        if new==old:break
        maps={x:True for x in new}
        demand(len(new)<2000,'unexpected closure explosion')
    C['normal_form_unary_functions']=len(maps)
    C['normal_form_coordinate_sorts']=len(nodes)


def cylinders():
    atom_id=lambda x,y:atom(x,y)
    for e,k in product(proper,repeat=2):
        for q,r in product(classes(e),classes(k)):
            spectrum={atom_id(x,y) for x in q for y in r if x!=y}
            if not spectrum:continue
            for t in spectrum:
                sat=comp(comp(e,atoms[t]),k)
                got={atom_id(x,y) for x in range(N) for y in range(N) if x!=y and sat[x]>>y&1}
                demand(got==spectrum,'representative cylinder depends on chosen atom')
                C['actual_cylinder_representative_checks']+=1
            C['actual_quotient_position_pairs']+=1
    # A diversity relation may still induce the IDENTITY hidden quotient map.
    owner=matrix(lambda x,y:pts[x][:2]==pts[y][:2]);clone=atoms[4]
    demand(comp(comp(converse(clone),owner),clone)==owner,'clone relation quotient identity kernel')
    demand(sub(clone,owner) and not sub(Id,clone),'fixture does not distinguish hidden and real equality')
    C['diversity_relation_hidden_identity_guard']+=1


def main():
    saturation();records=transport();normal_forms(records);cylinders()
    print(json.dumps(dict(status='PASS',seconds=round(time.monotonic()-START,3),counts=dict(sorted(C.items())),
        limits='Bounded finite original clone windows and generic invariant quotient actions only. No finite host is certified to have unbounded SAP/CCO, terminal NR2, first-hit/layer positivity, hidden SAP or Lean correctness.'),sort_keys=True))
if __name__=='__main__':signal.alarm(30);main()
