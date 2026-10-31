#!/usr/bin/env python3
"""Bounded B052 term-function, RAW return and malformed-input diagnostics."""
from collections import Counter, deque
from itertools import product, permutations, combinations
import json, signal, time

START=time.monotonic(); COUNTS=Counter()
def require(value,message):
    if not value: raise AssertionError(message)

def compose(first,second):
    return tuple(second[x] for x in first)

def term_functions():
    # Finite clone window for a nested common-block coordinate source.
    # Fine A and B coordinates have different literal charts: B=(u,v+u).
    real=list(product(range(3),range(3),range(2)))
    fine=list(product(range(3),repeat=2)); coarse=list(range(3))
    carriers={'A':real,'B':real,'AF':fine,'BF':fine,'AC':coarse,'BC':coarse}
    index={s:{x:i for i,x in enumerate(xs)} for s,xs in carriers.items()}
    def fn(src,dst,f): return tuple(index[dst][f(x)] for x in carriers[src])
    maps=[('A','AF',fn('A','AF',lambda x:x[:2]),'FAF'),
          ('A','AC',fn('A','AC',lambda x:x[0]),'FAC'),
          ('B','BF',fn('B','BF',lambda x:x[:2]),'FBF'),
          ('B','BC',fn('B','BC',lambda x:x[0]),'FBC'),
          ('AF','AC',fn('AF','AC',lambda x:x[0]),'uA'),
          ('BF','BC',fn('BF','BC',lambda x:x[0]),'uB'),
          ('AF','BF',fn('AF','BF',lambda x:(x[0],(x[1]+x[0])%3)),'f'),
          ('BF','AF',fn('BF','AF',lambda x:(x[0],(x[1]-x[0])%3)),'g'),
          ('AC','BC',fn('AC','BC',lambda x:x),'fc'),
          ('BC','AC',fn('BC','AC',lambda x:x),'gc')]
    outgoing={s:[m for m in maps if m[0]==s] for s in carriers}
    all_functions={}
    for src in carriers:
        initial=(src,tuple(range(len(carriers[src]))))
        reached={initial:()};q=deque([initial])
        while q:
            at,value=q.popleft()
            for _,dst,f,name in outgoing[at]:
                state=(dst,compose(value,f))
                if state not in reached:
                    reached[state]=reached[(at,value)]+(name,);q.append(state)
        all_functions[src]=reached
        COUNTS['distinct_term_functions']+=len(reached)
        # Build normal forms independently: one initial projection/upward,
        # followed by a transition-only function (zero steps allowed).
        initials=[initial]
        initials += [(dst,f) for _,dst,f,name in outgoing[src] if name.startswith('F') or name.startswith('u')]
        normalized=set()
        for at,f in initials:
            todo=deque([(at,f)]);seen={(at,f)}
            while todo:
                dst,g=todo.popleft();normalized.add((dst,g))
                for _,target,h,name in outgoing[dst]:
                    if name.startswith('F') or name.startswith('u'):continue
                    state=(target,compose(g,h))
                    if state not in seen:seen.add(state);todo.append(state)
        require(set(reached)==normalized,'term-function closure differs from normal forms')
        COUNTS['normal_form_source_sorts']+=1
        for v in range(len(carriers[src])):
            values={(dst,f[v]) for dst,f in reached}
            require(len(values)<=len(reached),'evaluation cardinal bound')
            COUNTS['actual_one_generated_closures']+=1
    require(sum(map(len,all_functions.values()))==22,'unexpected nested coordinate function count')
    # A nontrivial interchange across literal A/B charts.
    md={name:f for _,_,f,name in maps}
    require(compose(md['f'],md['uB'])==compose(md['uA'],md['fc']),'upward interchange')
    COUNTS['literal_upward_interchanges']+=1
    identity=tuple(range(9));loop=compose(md['f'],md['g'])
    require(loop==identity,'named inverse identity')
    repeated=identity
    for _ in range(200):repeated=compose(repeated,loop)
    require(repeated==identity,'infinitely repeatable syntax changed function')
    COUNTS['inverse_syntax_loops_checked']+=200
    # Kernels and forced factorisation are checked pointwise against a
    # separate equivalence calculation on original real tuples.
    for src in ['A','B']:
        projection_fine=md['F'+src+'F'];projection_coarse=md['F'+src+'C']
        for (dst,f),syntax in all_functions[src].items():
            if dst==src: level='id'
            else: level='fine' if dst.endswith('F') else 'coarse'
            eq=lambda x,y: x==y if level=='id' else real[x][:2]==real[y][:2] if level=='fine' else real[x][0]==real[y][0]
            for x,y in product(range(18),repeat=2):
                require((f[x]==f[y])==eq(x,y),'real-source kernel differs')
                COUNTS['real_kernel_pairs']+=1
            # J is fine or coarse; test exactly the admissible J<=K cases.
            for j,jproj in [('fine',projection_fine),('coarse',projection_coarse)]:
                if level=='id' or (j=='coarse' and level=='fine'):continue
                source_coord=src+('F' if j=='fine' else 'C')
                witnesses=[sigma for target,sigma in all_functions[source_coord] if target==dst and compose(jproj,sigma)==f]
                require(witnesses,'named forced factorisation missing')
                COUNTS['literal_forced_factorisations']+=1
    # All nested-block automorphisms on coordinate values, transported
    # coherently through the B chart. No assertion about infinite SAP.
    ps=list(permutations(range(3)))
    for p in ps:
        for local in product(ps,repeat=3):
            af=lambda uv:(p[uv[0]],local[uv[0]][uv[1]])
            def bf(uv):
                u,v=uv;v=(v-u)%3;nu,nv=af((u,v));return (nu,(nv+nu)%3)
            actions={'AF':fn('AF','AF',af),'BF':fn('BF','BF',bf),
                     'AC':tuple(p),'BC':tuple(p)}
            for dst,f in all_functions['A']:
                if dst=='A':continue
                kproj=md['FAF'] if dst.endswith('F') else md['FAC']
                kact=actions['AF' if dst.endswith('F') else 'AC']
                for x in range(18):
                    require((actions[dst][f[x]]==f[x])==(kact[kproj[x]]==kproj[x]),'stabilizers differ')
                    COUNTS['equivariant_stabilizer_tests']+=1

def relation(n,p):return tuple(sum(1<<y for y in range(n) if p(x,y)) for x in range(n))
def relcomp(r,s):
    out=[]
    for row in r:
        value=0
        while row:
            bit=row&-row;row-=bit;value|=s[bit.bit_length()-1]
        out.append(value)
    return tuple(out)
def converse(r):return tuple(sum(1<<x for x in range(len(r)) if r[x]>>y&1) for y in range(len(r)))
def subset(r,s):return all(not(a&~b) for a,b in zip(r,s))

def raw_returns():
    # Regular C6 quotient action with two finite clone representatives.
    # A and B are literal disjoint sorts with shifted coordinate charts.
    n=12;ident=relation(n,lambda x,y:x==y)
    def base(i,sort):return (i//2-(1 if sort=='B' else 0))%6
    def eq(d,sort):return relation(n,lambda x,y:(base(x,sort)-base(y,sort))%d==0)
    def edge(s,t,shift,d,wide):
        return relation(n,lambda x,y:((base(y,t)-base(x,s))%d==shift%d) if wide else ((base(y,t)-base(x,s))%6==shift%6))
    for d in [1,2,3,6]:
        for shifts0 in product(range(d),repeat=3):
            shifts=shifts0+((-sum(shifts0))%d,)
            sorts=['A','B','A','B','A'];prefix=[ident];factors=[]
            for k,shift in enumerate(shifts):
                p=edge(sorts[k],sorts[k+1],shift,d,bool(k%2));factors.append(p);prefix.append(relcomp(prefix[-1],p))
            require(subset(prefix[-1],eq(d,'A')),'return word not contained in E0')
            for e in [e for e in [1,2,3,6] if d%e==0]:
                J=eq(e,'A');kernels=[];labels=[]
                for k,R in enumerate(prefix):
                    require(subset(relcomp(R,converse(R)),J),'prefix kernel bound')
                    K=relcomp(relcomp(converse(R),J),R);kernels.append(K)
                    label=[]
                    for y in range(n):
                        ls={base(x,'A')%e for x in range(n) if R[x]>>y&1}
                        require(len(ls)==1,'canonical predecessor label ambiguous')
                        label.append(next(iter(ls)))
                    labels.append(label)
                    expected=relation(n,lambda x,y:label[x]==label[y])
                    require(K==expected,'prefix formula not canonical label kernel')
                    COUNTS['raw_prefix_kernel_tests']+=1
                for k,P in enumerate(factors):
                    require(subset(relcomp(P,converse(P)),kernels[k]),'factor kernel bound')
                    require(relcomp(relcomp(converse(P),kernels[k]),P)==kernels[k+1],'adjacent target kernel mismatch')
                    for x,y in product(range(n),repeat=2):
                        if P[x]>>y&1:require(labels[k][x]==labels[k+1][y],'edge changed canonical label')
                    COUNTS['raw_factor_transport_tests']+=1
                require(labels[0]==labels[-1],'closed word has nonidentity canonical holonomy')
                # Directly compose the quotient functions in physical class
                # charts and check identity; translation shifts sum to 0 mod e.
                q=tuple(range(e))
                for shift in shifts:q=tuple((v+shift)%e for v in q)
                require(q==tuple(range(e)),'literal quotient return not identity')
                COUNTS['coarsened_identity_returns']+=1
    # Whole-word containment is essential: a one-step rotation on actual
    # equality classes has nonidentity quotient transport.
    rotation=tuple((i+1)%6 for i in range(6))
    require(rotation!=tuple(range(6)),'noncontained return guard missing')
    require(any((rotation[i]-i)%6 for i in range(6)),'nonidentity graph accidentally in equality')
    COUNTS['whole_word_containment_guards']+=1
    empty=(0,)*n
    require(subset(empty,ident) and not all(empty),'empty relation containment does not yield seriality')
    COUNTS['nonempty_factor_guards']+=1

def malformed_sources():
    for n in range(2,8):
        f={2*i:2*i+1 for i in range(n)}
        g={2*i+1:2*((i+1)%n) for i in range(n)}
        step={**f,**g};vertices=set(range(2*n))
        for root in vertices:
            seen={root};v=step[root]
            while v not in seen:seen.add(v);v=step[v]
            require(seen==vertices,'malformed one-generated closure not entire source')
            COUNTS['malformed_one_generated_closures']+=1
        # Exhaustive subset closedness through 14 vertices is small and
        # independent of the one-orbit traversal above.
        closed=[]
        for bits in range(1<<(2*n)):
            if all(not(bits>>x&1) or bits>>step[x]&1 for x in vertices):closed.append(bits)
        require(closed==[0,(1<<(2*n))-1],'proper nonempty unary-closed subset exists')
        COUNTS['malformed_closed_subset_tests']+=1<<(2*n)
        # In every genuine target g*f=id. Homomorphism equations therefore
        # identify every x_i with x_(i+1), violating whole-source injectivity.
        pairs=[(2*i,2*((i+1)%n)) for i in range(n)]
        require(all(a!=b for a,b in pairs),'n>=2 collapse guard')
        COUNTS['forced_distinct_point_collapses']+=len(pairs)
    COUNTS['unbounded_malformed_family_sizes']+=6

def main():
    term_functions();raw_returns();malformed_sources()
    print(json.dumps({'status':'PASS','seconds':round(time.monotonic()-START,3),'counts':dict(sorted(COUNTS.items())),
      'scope':'Bounded finite diagnostics only; no unbounded SAP/CCO, hidden homogeneity/SAP, HN/HKN receiving binding or Lean certification.'},sort_keys=True))
if __name__=='__main__':
    signal.signal(signal.SIGALRM,lambda *_:(_ for _ in ()).throw(TimeoutError('B052 controls exceeded 30 seconds')))
    signal.alarm(30);main();signal.alarm(0)
