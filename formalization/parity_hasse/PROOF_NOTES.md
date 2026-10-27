# Sparse graphs, original parity/Hasse and independent exact gates

This is mathematical preparation for other Lean projects. The machine DAG
and source hashes are in `module.json`; nothing here is a compiled Lean API.
The two source files contribute seven result exports. Quotient-word and
bridge definitions have additional source snapshots. No human TeX is edited.

## N01: Finite labelled probability space

Let q,r,g be positive integers and replace g by max(g,3). Let log be the
natural logarithm. Set c=128rq log(q+1), and independently label each
unordered pair of n vertices by 0,1,...,r with probabilities 1-c/n and
c/(nr) for each positive label. Take n>c, so all probabilities are valid.
This is a finite product probability space; each positive label produces
one edge, so the graph is simple and no pair has two labels.

For a colouring kappa and a choice h of one label per vertex colour, count
the same-colour pairs carrying the requested label. If the colour classes
have sizes n_d, then
N=(sum_d n_d²-n)/2 >= (n²/q-n)/2 >= n²/(4q) for n>=2q.
Empty colour classes are permitted. Each relevant pair independently has
the required label with probability p=c/(nr), even when different pairs
ask for different labels. Thus mu=Np>=cn/(4rq).

## N02: Tail, finite union and an explicit sufficient n

For X the above sum, independence gives
E(exp(-X))=(1-p+p exp(-1))^N <= exp(-Np/2), using exp(-1)<=1/2.
Markov at exp(-mu/4) bounds Pr(X<mu/4) by exp(-mu/4), hence by
exp(-cn/(16rq)). This derives the required tail estimate; there is no
Chernoff theorem import.

There are q^n r^q pairs (kappa,h). Put
delta=c/(16rq)-log q=8log(q+1)-log q>0 and
B=sum_{ell=3}^g c^ell/(2ell)>0.
It suffices to choose an integer n with

- n>=2q and n>c;
- n>(q log r+log 4)/delta;
- n>64rqB/c.

Then the union-bound failure probability is at most r^q exp(-delta n)<1/4
and every mu/4>=cn/(16rq)>4B. Archimedean integer choice suffices; no
optimized bound or limiting probability theorem is needed. q=r=1 works.

For each ell<=n, the expected number of unoriented simple ell-cycles is
(n)_ell/(2ell) times (c/n)^ell, at most c^ell/(2ell). Lengths ell>n
contribute zero. Linearity of expectation gives at most B short cycles;
Markov bounds Pr(number>4B) by 1/4. Independence between the two global
events is not needed. Their intersection has probability greater than 1/2.

## N03: Deletion and the graph actually consumed by parity

Choose an outcome satisfying both events. Repeatedly delete an edge of a
remaining short cycle. Deletion creates no cycle; each step destroys a
different original cycle, so there are at most 4B deletions. Each X loses
at most one per deleted edge, hence remains positive. If the labelled
conclusion failed, choose for each colour d a missing monochromatic label
h(d); then the corresponding X would be zero. Unused colours cause no
problem, since r>=1.

Set r=1 to obtain a graph with no proper q-colouring and girth>g. To obtain
the connected graph used in parity, take a connected component that still
has no proper q-colouring. Otherwise colour the finitely many components
and combine their colourings. This extraction is used only after r=1;
it need not preserve the full multicolour labelled property for r>1.

## N04: Elementary original relation and index geometry

Work on one inhabited original real sort. Homogeneity/completeness identify
the finitely many named atoms, including Id, with actual pair orbitals.
Transitivity makes nonempty invariant relations serial and coserial.
All orbitals are symmetric; therefore every invariant relation, including
a represented product, is symmetric. Taking converse gives RS=SR. It is
not enough merely to say that equivalence relations are symmetric.

Invariant equivalences permute; their join is their actual product. The
full lattice is finite and modular, not generally distributive. Define
[F:E] as the number of E-classes in one F-class. Original transitivity
makes this uniform. A finite index in a containing interval makes every
intermediate factor finite, and indices multiply along a finite chain.

For invariant E and X, put F=E join X and K=E meet X. The transposition
between [K,X] and [E,F] is T -> E join T with inverse U -> U meet X.
Prove the modular identities, then the order isomorphism and cover transfer.
Numerical index equality is a separate fact: for a fixed point a, map
X[a]/K to F[a]/E by sending a K-class to its E-class. Injection uses
K=E meet X; surjection uses F=EX. Thus [X:K]=[F:E]. Do not infer this
class bijection merely from an abstract lattice isomorphism.

## N05: Orbital bipartiteness and RAW parity profiles

For invariant E<F with n=[F:E]<infinity and atom c<=F\E, suppose the
c-graph has an odd cycle of length ell. Use N03 with q=n,g=ell and take
its connected high-chromatic component G. Every specified cycle maps to
the old c-graph: even cycles fold onto one c-edge, and an odd cycle of
length k>ell traverses the old ell-cycle with (k-ell)/2 backtracks.
Use semantic homomorphic CCO to map G into the original source. Its image
lies in one F-class by connectedness; its E-classes supply a proper
n-colouring, contradiction. No SAP, exact Helly or injective map is used.

Seriality gives Id<=c², and backtracks give c^j<=c^(j+2), including j=0.
Finite orbital supports stabilize the even and odd chains. Choose a common
bound with a **positive even exponent**: Y=c^(2N), O=c^(2N+1).
These equal all even and odd walk relations, including length-zero walks
in Y. Both are nonempty exact single-word profiles. Bipartiteness makes
them disjoint; X=Y union O is connectivity. Each component has precisely
two Y-classes, since seriality excludes isolated vertices. Hence Y<X<=F,
[X:Y]=2 and X is not <=E. X need not be exact; Y need not contain E.

## N06: Full Hasse covers and powers of two

Induct on the height of the upper endpoint F in the finite **full**
invariant-equivalence lattice. For a finite-index cover E<F choose the
parity seed Y<X<=F from N05. Since X is not <=E, E join X=F.
Let K=E meet X; N04 gives K<X a cover and [X:K]=[F:E].

If K=Y, finish. Otherwise K,Y are distinct coatoms of X and join to X.
Put L=K meet Y; a second transposition gives L<Y a cover and
[Y:L]=[X:K]. Its upper endpoint Y is strictly below F, so induction
applies. This does not require E,F,K,L,X to be exact.

For a general finite [F:E], choose a saturated chain and multiply its
finite cover indices. E=F gives the empty product 1=2^0. A singleton
source has no strict interval, so causes no exception. This proof uses
neither exact convolution nor RAW Helly; the DAG enforces that separation.

## N07: Relative powers and least witnesses for separation

Now use the imported RAW exact product/three-set Helly contract. For exact
equivalence K and symmetric exact K-bisaturated A containing K, define
A^[0]=K and A^[n]=A^n for n>0. K is the unit on these saturated relations,
so A^[n+1]=A^[n];A also at n=0. Powers contain K and increase. Finitely
many supports give a stable exact equivalence <A>. Do not replace the
relative zeroth power with Id when K is nontrivial.

If <A> meet <B> exceeds K, minimize n>=1 with B^[n] meet <A> outside K,
choose an atom c there, then minimize m>=1 with c<=A^[m]. Suppose
c<=A^[m-1];B^[n-1], witnessed atomically by a,b. Peirce puts
b<=a^converse;c<=<A>. If b is outside K, n-minimality fails; when n=1,
B^[0]=K makes that branch impossible. If b<=K, saturation puts
c<=A^[m-1], contradicting m-minimality, also when m=1.

## N08: The three-domain Helly contradiction

Set T=A^[m-1];c;B^[n-1]. The arbitrary atom c need not be K-saturated.
The **outer factors** supply K;T;K=T. Both contain Id, so c<=T and T is
nonempty. Product closure gives exactness. Peirce applied to
c<=A^[m-1];A makes T meet A; the analogous B rotation makes T meet B.

If T meets K, bisaturation gives a diagonal pair in T; invariance and
transitivity then give all Id<=T. Rotating such a witness and using
symmetry gives c<=A^[m-1];B^[n-1], the excluded relation. Thus T avoids K.
But A meet B=K is nonempty, so A,B,T meet pairwise and have empty total
intersection, contradicting RAW exact 2-Helly. This is a three-domain
support instance, not heterogeneous ball Helly or CRT. K=Id gives the
identity corollary. This branch does not use Hasse or graph probability.

## N09: An independent maximal exact gate

Take invariant Y<X of relative index two with Y and O=X\Y exact.
X need not be exact. Choose an inclusion-maximal exact equivalence K
with Y<=K and K meet X=Y; the finite candidate set contains Y.
Transposition gives [K join X:K]=2. Put F=K join X, t=K;O;K.
Since X=Y union O, F=K disjoint-union t; t is nonempty exact and
K-bisaturated. O;O=Y by the two-sheet geometry, and original commutation
gives t;t=K. On quotient classes, t/K is an invariant total fixed-point-free
involution, hence a single actual pair orbital by quotient transitivity.

On real points t is generally a complete bipartite relation between paired
K-classes, **not** a functional graph. No representative-selection map
or group section is produced.

For any original exact equivalence Z>K, the equivalence Z meet X lies
between Y and X. If it is Y, Z is a larger admissible candidate, impossible.
Otherwise it is X, so O<=Z and t<=Z. This uses maximality among all original
exact candidates. It does not use closure separation, Hasse, exact-lattice
distributivity or an exactness assertion about X.

## N10: Quotient pullback and the bridge export

For the actual quotient q:M->M/K name every actual orbital of the original
group action. The pullback of the orbital of (q(x),q(y)) is K;a;K for
the actual old orbital a of (x,y): move the output pair by one original
automorphism and change its representatives inside their K-classes.
Thus atomic pullbacks are exact. Quotient equality pulls back to K, and
Top to Top. Surjectivity of q makes pullback commute with represented
composition: a quotient intermediate class has a real representative, and
endpoint saturation removes any discrepancy between witnesses. Induction
on words and ordinary inverse-image intersections prove exact pullback.
This independently expands the single-sort part of
`lem:typed-simultaneous-blocks`; no full quotient-lifting theorem is needed.

Consequently a nontrivial exact quotient equivalence pulls back to an
original exact Z>K, so contains t/K by N09. Already at the original level
K;t=t, t;t^converse=K and t^converse;t=K: t is a nonidentity bridge at
kernel K under `def:foundational-exact-bridge`. The rigid-character theorem
is a later consumer of this export, never an imported premise or a cycle.
