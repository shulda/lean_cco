#!/usr/bin/env python3
"""Bounded B056 diagnostics, not a CCO/SAP or infinite obstruction certificate."""
from itertools import product,combinations,permutations
from collections import deque

M=list(product(range(3),range(3),range(2)))
def termvals(kind,x):
    r,c,k=x
    if kind=='real':return [('real',x),('row',r),('row_twin',r),('col',c)]
    if kind=='row':return [('row',r),('row_twin',r)]
    return [('col',c)]
def orbital(x,y):
    a,v=x;b,w=y
    if x==y:return ('EQ',a)
    if a=='real' and b=='real':return ('RR',v[0]==w[0],v[1]==w[1])
    if a=='real':return ('RQ',b,v[0 if b.startswith('row') else 1]==w)
    if b=='real':return ('QR',a,v==w[0 if a.startswith('row') else 1])
    if a.startswith('row') and b.startswith('row'):return ('ROWS',a,b,v==w)
    if a=='col' and b=='col':return ('COLS',False)
    return ('CROSS',a,b)
def atom(x,y):
    assert x!=y
    return (x[0]==y[0],x[1]==y[1])

def all_term_profiles():
    witnesses={}
    for x,y in product(M,repeat=2):
        if x!=y:witnesses.setdefault(atom(x,y),(x,y))
    tests=0;comparisons=0;survivors=0
    for ka,kb in product(['real','row','col'],repeat=2):
        sigs={}
        for t,(x,y) in witnesses.items():
            aa=termvals(ka,x);bb=termvals(kb,y)
            sigs[t]=tuple(orbital(a,b) for a,b in product(aa,bb))
        # Every old atomic type determines every root term-pair comparison.
        for x,y in product(M,repeat=2):
            if x==y:continue
            actual=tuple(orbital(a,b) for a,b in product(termvals(ka,x),termvals(kb,y)))
            assert actual==sigs[atom(x,y)];tests+=1
        for t0,sig in sigs.items():
            profiles=[{t for t,s in sigs.items() if s[i]==v} for i,v in enumerate(sig)]
            common=set.intersection(*profiles)
            assert t0 in common
            assert all(sigs[t]==sig for t in common)
            # Complete record of a different local type cannot be accepted.
            for t in set(sigs)-common:assert sigs[t]!=sig
            comparisons+=len(profiles);survivors+=len(common)
    # Source descendant join does not make its real ancestors irreducible.
    closures={'x':{'x','u'},'y':{'y','v'},'u':{'u'},'v':{'v'}}
    relations=[('u','v')]
    left={'x','u','v'};right={'y','u','v'};base={'u','v'}
    assert left&right==base and left|right==set(closures)
    for factor in (left,right,base):
        assert all(closures[z]<=factor for z in factor)
    assert all(set(t)<=left or set(t)<=right for t in relations)
    assert not {'x','y'}<=left and not {'x','y'}<=right
    # Pairwise overlap alone does not construct one actual common survivor.
    P=[{0,1},{1,2},{0,2}]
    assert all(a&b for a,b in combinations(P,2)) and not set.intersection(*P)
    return tests,comparisons,survivors

def simple_cycles(V,E):
    for n in range(3,len(V)+1):
        for vs in combinations(V,n):
            a=min(vs)
            for p in permutations([v for v in vs if v!=a]):
                if p[0]>=p[-1]:continue
                c=(a,)+p
                ce={frozenset((c[i],c[(i+1)%n])) for i in range(n)}
                if ce<=E:yield c,ce

def private_graphs():
    count=0
    for config in [((0,1),(1,2),(2,0)),((0,1),(0,1),(1,2),(2,0)),((0,1),(1,2),(2,3),(3,0),(0,2))]:
        roots=set().union(*(set(x) for x in config));nxt=max(roots)+1
        V=set(roots);E=set();paths=[]
        for i,(p,q) in enumerate(config):
            # Two branch lengths, private interiors; repeated theta endpoint
            # pairs are allowed, but direct graph edges are merged naturally.
            for length in (1,2+(i%2)):
                path=[p]+list(range(nxt,nxt+length-1))+[q];nxt+=length-1
                V.update(path);pe={frozenset((a,b)) for a,b in zip(path,path[1:])};E|=pe
                paths.append((p,q,set(path[1:-1]),pe))
        # Restrict test sizes to keep this diagnostic bounded.
        assert len(V)<=12
        # DFS cycles avoids enumerating permutations of nonedges.
        def dfs(start,cur,path):
            nonlocal count
            for z in sorted(v for e in E if cur in e for v in e if v!=cur):
                if z==start and len(path)>=3:
                    if path[1]>path[-1]:continue
                    ce={frozenset((path[i],path[(i+1)%len(path)])) for i in range(len(path))}
                    count+=1
                    for p,q,inside,pe in paths:
                        if inside&set(path):assert pe<=ce and {p,q}<=set(path)
                elif z>start and z not in path:dfs(start,z,path+[z])
        for start in sorted(V):dfs(start,start,[start])
    # Adding an outside interior edge breaks the entire-branch property.
    pe={frozenset(e) for e in [(0,3),(3,1),(0,4),(4,1)]}
    bad=pe|{frozenset((3,2)),frozenset((2,0))}
    c={frozenset(e) for e in [(0,3),(3,2),(2,0)]}
    assert c<=bad and not {frozenset((0,3)),frozenset((3,1))}<=c
    return count

def typed_profile_states():
    # Actual finite relation products on two tagged copies of regular Z3.
    # A typed state is (source,end,nonempty difference menu).
    atoms=[(0,1,frozenset({1})),(1,0,frozenset({1}))]
    seen={};queue=deque()
    for s in atoms:seen.setdefault(s,[s]);queue.append(s)
    def mul(s,t):
        assert s[1]==t[0]
        return s[0],t[1],frozenset((a+b)%3 for a,b in product(s[2],t[2]))
    while queue:
        s=queue.popleft()
        for t in atoms:
            if s[1]!=t[0]:continue
            v=mul(s,t)
            if v not in seen:seen[v]=seen[s]+[t];queue.append(v)
    # The restricted alphabet generates witnesses up to length six, so
    # shortest-prefix checks genuinely require several nonempty states.
    assert max(map(len,seen.values()))==6
    for s,word in seen.items():
        prefixes=[];v=None
        for t in word:v=t if v is None else mul(v,t);prefixes.append(v)
        assert len(prefixes)==len(set(prefixes)) and len(word)<=len(seen)
    # Delete a repeated positive prefix state in a longer compatible word.
    word=atoms*9;prefixes=[];v=None
    for t in word:v=t if v is None else mul(v,t);prefixes.append(v)
    i,j=next((i,j) for i,j in combinations(range(len(prefixes)),2) if prefixes[i]==prefixes[j])
    shortened=word[:i+1]+word[j+1:]
    assert 0<len(shortened)<len(word)
    v2=None
    for t in shortened:v2=t if v2 is None else mul(v2,t)
    assert v2==v
    # Equal untyped menus on different current sorts cannot be interchanged.
    s=(0,0,frozenset({1}));t=(0,1,frozenset({1}));suffix=(0,0,frozenset({2}))
    assert s[2]==t[2] and s[1]!=t[1] and s[1]==suffix[0] and t[1]!=suffix[0]
    return len(seen)

def block_profiles():
    # Full RAW orbital algebra for infinitely many blocks/two bits/infinite
    # clones, computed using a sufficiently large explicit triangle window.
    X=list(product(range(4),range(2),range(4)))
    def colour(x,y):
        if x==y:return 'Id'
        if x[0]!=y[0]:return 'r'
        return 'p' if x[1]==y[1] else 'q'
    table={}
    for a,b in product(['p','q','r','Id'],repeat=2):
        out=set()
        for x,y in product(X,repeat=2):
            if colour(x,y)!=a:continue
            for z in X:
                if colour(y,z)==b:out.add(colour(x,z))
        table[a,b]=out
    menus={frozenset({a}) for a in ['p','q','r','Id']};queue=deque(menus)
    while queue:
        P=queue.popleft()
        for a in ['p','q','r','Id']:
            Q=frozenset().union(*(table[b,a] for b in P))
            if Q not in menus:menus.add(Q);queue.append(Q)
    assert frozenset({'p','q'}) not in {P-{'Id'} for P in menus}
    candidates=[P for P in menus if {'p','q'}<=P]
    assert candidates and all('r' in P for P in candidates)
    assert 'r' in set.intersection(*map(set,candidates))
    assert table['q','q']=={'Id','p'} and table['p','q']=={'q'}
    return len(menus),len(candidates)

if __name__=='__main__':
    a,b,c=all_term_profiles();g=private_graphs();s=typed_profile_states();m,n=block_profiles()
    print(f'PASS B056: {a} actual pair readouts/{b} complete comparisons/{c} common spectra; {g} private cycles; {s} typed positive states; {m} RAW word menus/{n} p+q containing menus. Bounded diagnostics only.')
