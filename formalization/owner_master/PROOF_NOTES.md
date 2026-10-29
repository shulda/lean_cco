# Simultaneous finite exact-owner master — expanded proof notes

Source `490c3f36d85db5a0b3ced0598e6c431825254ec5`. Complete preparation of
`thm:acf-owner-master` for OTHER receiving Lean projects. No human TeX or
mathematical Lean is edited here. `module.json` contains the source hashes,
quantified contracts, claim DAG, import and article-feedback ledgers.

## N00: Scope and two different inductions

The source theorem is CONDITIONAL on ordinary EPPA for EVERY actual exact
quotient, including the original source. Its finite master cannot be used
to prove that same input. The abstract finite upset-diagram/CRT argument
is independent of CCO, exactness, countability, EPPA, groups, SAP and NR2.
The actual source instantiation separately supplies all decorated callbacks.
A-node premises are branch-specific quantified theorem arguments; they are
not a conjunction silently assumed in every source theorem. At C25 the
local abstract inputs are discharged by the cited constructed providers.

The source M1–M4 proof passes this bounded review under its explicit provider
premises. This pass expands its
coherent ONTO quotient-system invariant, canonical double quotient colours,
all finite indexed family cases, and full finite-group actions. These are
proof expansions, not strengthened source hypotheses. Choose p MAXIMAL in P minus U, equivalently minimal in the extended
processed upset U union {p}. Every subscripted old diagram object is then
available.

The actual import path retains the current countable joint exact lifting
and quotient-source providers. Countability is not needed by the generic
finite diagram theorem or its pure group quotient lemma. No global lift
Aut(quotient)->Aut(source), no selected ambient subgroup in place of full
finite Aut, and no group section is assumed.

## N01: Max-first order and every available upset

Choose p maximal in the nonempty complement P\U. Such p exists by
finiteness. Every q>p belongs to U, so O is an old upset. The set O union
{p} is the principal upset ↑p. The new S=U union {p} is an upset: the
only new upward-closure check is that successors of p already lie in U.

No element q<p lies in U, since upward closure of U would put p in U.
Consequently p is minimal in S. If a new upset V subset S contains p,
then ↑p subset V, so O subset V^-. The set V^- is an upset of P: if
q belongs to V^- and q<=r, upward closure gives r in V; r=p would imply
q<p, impossible because q belongs to U, so r belongs to V^-.

Thus every subscript used in the product and map formulas is defined in
the OLD diagram. Every upset of S is either an old upset of U or a new
one containing p; none is omitted. In particular, the largest new object
is B_S=B_U x_{B_O} D_p. The construction has precisely |P| stages and at
most one local provider invocation at each stage.

P empty is legitimate. The abstract final system is the singleton B_empty.
In the actual bounded exact lattice, P empty means Id=Top; since X is
inhabited, X is a singleton, so the source conclusion is immediate with
zero provider calls.

## N02: Abstract diagram invariant, full carriers and initial object

Let P be a finite poset. Write Up(P) for its upsets. Choose an enumeration
p_1,...,p_n such that q>p_i implies q occurs before p_i. Put S_0=empty,
S_k={p_1,...,p_k}. Thus every S_k is an upset. At stage k, the diagram is
indexed by ALL upsets V of P contained in S_k, not merely by the chain of
S_j or by principal upsets.

Construct sets B_V and maps r_{V,W}:B_V -> B_W for W subset V as follows.
Begin with B_empty a singleton and its identity map. For the next element
p, put U=S_k, S=U union {p}, O={q:q>p}. Choose ANY nonempty finite set D_p
with an onto map e_p:D_p -> B_O. (The “finite” condition is needed for a
finite final witness, not for the CRT argument.) Keep every old B_V and
every old map unchanged. If p belongs to V subset S, put V^-=V\{p} and

    B_V = {(b,x) in B_{V^-} x D_p : r_{V^-,O}(b)=e_p(x)}.

The notation identifies B_{O union {p}} canonically with D_p. One may use
that canonical bijection, or retain B_O x_{B_O} D_p literally; do not
mistake definitional equality for a needed extra hypothesis.

Define the new maps by the following exhaustive cases:

1. V,W old: retain r_{V,W}.
2. V new, W old, W subset V: r_{V,W}(b,x)=r_{V^-,W}(b).
3. V,W new, W subset V: r_{V,W}(b,x)=(r_{V^-,W^-}(b),x).

An old V cannot have a new W below it. The theorem is that these data form
a coherent diagram of nonempty finite sets, all r_{V,W} are surjective,
and for EVERY finite indexed family (V_i)_{i in I}, including I empty,

    B_{union_i V_i} -> { (b_i) in product_i B_{V_i} :
      r_{V_i,V_i intersection V_j}(b_i)
       =r_{V_j,V_i intersection V_j}(b_j) for all i,j }

is a bijection, via the natural projections.

No relational structure, group action, exact equivalence, countability,
distributive-equivalence theorem, EPPA, packet closure, SAP or section
belongs in this abstract theorem. It is a recursively constructed finite
diagram theorem. Alternatively one can state it for a preexisting coherent
upset diagram having these pullback squares at every stage; the same proof
then verifies all-family CRT. Merely asking for onto maps is insufficient.

For the decorated source base, X_empty=X/Top is a singleton. Since A is
nonempty, A_empty is that singleton. Every partial automorphism (empty or
identity) extends, its full finite packet is the singleton, its automorphism
group is trivial, and every finite family of its copies has one compatible
tuple. In the abstract set theorem the singleton B_empty is an explicit
input; onto maps alone do not force it.

## N03: Canonical maps before any CRT or group argument

Well-definedness of case 3 follows from old coherence:

    r_{W^-,O}(r_{V^-,W^-}(b)) = r_{V^-,O}(b) = e_p(x).

Cases 1 and 2 plainly land in the declared old object. The identity map
on a new object follows from r_{V^-,V^-}=id. For T subset W subset V,
check composition according to where p occurs:

* all three old: old coherence;
* V new, W,T old: old coherence on b;
* V,W new, T old: both composites forget x and return r_{V^-,T}(b);
* V,W,T new: both composites return (r_{V^-,T^-}(b),x).

These are exhaustive because p-membership is monotone along inclusions.
Hence r_{W,T} r_{V,W}=r_{V,T} everywhere.

Each new B_V is finite. It is nonempty: choose b in nonempty B_{V^-},
then use onto e_p to choose x over its owner. Both factor projections
B_V -> B_{V^-},D_p are onto, since r_{V^-,O} and e_p are onto.

All nested maps are onto. For V new and W old, lift a point of B_W to
B_{V^-} using old surjectivity, then lift its owner through e_p. For
V,W new, given (c,x) in B_W choose b in B_{V^-} with
r_{V^-,W^-}(b)=c. Because O subset W^-, coherence gives
r_{V^-,O}(b)=r_{W^-,O}(c)=e_p(x). Thus (b,x) is a preimage. The
old-old case is unchanged.

This establishes EXACTLY the additional invariant that 04's prose uses.
It does not appeal to M4 to establish the maps or their onto property,
so there is no induction circularity.

## N04: ALL finite-family CRT, existence AND uniqueness

Denote S_I=union_i V_i. Coherence always makes the natural coordinate
map land among pairwise compatible tuples; this forward direction must
be stated as part of the induction, not only the reconstruction direction.

If I is empty, S_I=empty, the empty product is a singleton, and B_empty
is a singleton. Thus the natural map is a bijection. This is independent
of all nonempty reconstruction arguments.

Now suppose I is nonempty. If p does not belong to S_I, all objects and
maps are old, and apply old CRT. Otherwise let J={i:p in V_i}, which is
nonempty. Given a compatible tuple (b_i), define

    c_i = b_i if i not in J,
          first-coordinate(b_i) if i in J,
    V_i^- = V_i\{p} for every i.

For i not in J this simply gives V_i^-=V_i. The coordinate c_i lies in
B_{V_i^-}. Project each assumed equality over B_{V_i intersection V_j}
to B_{(V_i intersection V_j)\{p}}. The target index equals
V_i^- intersection V_j^-, and the explicit map formulas show the images
are precisely the projections of c_i,c_j. This proves old pairwise
compatibility even when exactly one of i,j belongs to J; no map from an
old V_i to O is needed in that mixed case.

Old CRT gives a UNIQUE b in B_T, where T=union_i V_i^-, inducing every
c_i. Since J is nonempty, one V_i^- contains O, so O subset T.

For i in J write b_i=(c_i,x_i). If i,j belong to J then their
intersection still contains ↑p. Its new-object projection retains its
D_p coordinate, so compatibility implies x_i=x_j. Thus there is one
well-defined x in D_p. When |J|=1 this coordinate is determined by that
single b_i, without any pairwise argument.

Choose i_0 in J. Membership b_{i_0} in its full pullback says

    r_{V_{i_0}^-,O}(c_{i_0}) = e_p(x).

Since b projects to c_{i_0}, coherence gives r_{T,O}(b)=e_p(x).
Consequently (b,x) belongs to B_{T union {p}}=B_{S_I}. Its projections
are b_i: for old indices use its b-coordinate; for new indices use the
pair (c_i,x_i). This proves existence.

For uniqueness, any y in B_{S_I} has two coordinates (b',x'). Its
projections to every B_{V_i^-} are c_i, so old CRT uniqueness gives
b'=b. A single new index i_0 determines x'=x. Thus y=(b,x).

Special cases are now explicit:

* A one-member family gives the identity B_V -> B_V.
* Repeated upsets are allowed. Compatibility for two copies V_i=V_j
  is equality in B_V itself, because r_{V,V}=id, so the two prescribed
  coordinates must coincide. No distinct-index simplification is needed.
* V_i=empty is allowed, with its unique coordinate in B_empty. It
  imposes no extra restriction. A nonempty family of only empty upsets
  still has a unique realization.
* Incomparable upsets require no extra argument: their intersection
  is available at that stage, and the same two-coordinate removal works.
* Every relevant union and intersection is an upset contained in S.
* Pairwise compatibility can be imposed for all i,j, or only distinct
  i,j; diagonal conditions are identities.
* These are finite indexed families, not infinite-family compactness.
  Since the index lattice itself is finite, an arbitrary family of
  available indices can formally be reduced to distinct indices if one
  also uses repeated-coordinate equality; no such strengthening is
  needed or asserted in the source.

The induction proves CRT for ALL finite families at each stage, not only
for a preselected list, binary families, principal upsets, or the eventual
top object.

## N05: Canonical nested quotients, exact descent and fine colours

Let Lambda be the full finite bounded distributive lattice of actual
exact invariant equivalences. Use the Birkhoff representation
Lambda ~= Down(P) with NONZERO join-irreducibles P. For an upset V put
K_V=E_{P\V}, X_V=X/K_V. Then W subset V implies K_V subset K_W and
gives the canonical quotient map r^X_{V,W}. Its definition sends the
K_V-class of a real x to the K_W-class of x. This immediately proves
identity, composition and surjectivity of ambient maps.

For new V, the relevant original equivalences obey

    K_{V^-} intersection K_{↑p} = K_V,
    K_{V^-} join K_{↑p} = K_O,

because V^- union ↑p=V and V^- intersection ↑p=O. The actual two-factor
CRT bijection gives X_V ~= X_{V^-} x_{X_O} X_{↑p}. Exact fine-colour
readout is SEPARATE and upgrades this to the actual fine-colour
identification used by the owner product theorem. It is unnecessary for
the abstract all-family CRT theorem.

The actual finite subset definition is preferably expressed without
choosing coordinate representatives:

    B_V = {y in X_V : r^X_{V,V^-}(y) in B_{V^-}
                      and r^X_{V,↑p}(y) in D_p}.

The ambient actual pullback bijection identifies this induced subset with
the FULL finite fibre product, so it has exactly the maps in N03.
All finite maps are restrictions of the original actual quotient maps.
This makes their naturality independent of any arbitrary choice of set
bijections in Birkhoff or in product notation.

Retain the invariant A_V=pi_V(A) subset B_V. Indeed a point a in A_V
has the two actual images in A_{V^-} subset B_{V^-} and
A_{↑p} subset D_p; it therefore lies in the new full product. This
requires only that A is the original finite set. One must NOT assume
A_V is itself the full product of its two shadows; its sparsity is
allowed and matters in the M1 consumer.

At the end set B=B_P subset X_P=X. The proven projection surjectivity
gives pi_V(B_P)=B_V for every upset V. Thus the theorem's asserted
B_E=pi_E(B) is a conclusion of the induction; it is not merely a chosen
label for unrelated compatible witness sets. Because each B_V is its
actual finite induced subset, this equality identifies the structures
as well as their underlying sets.

For the exact-indexed M4, if E_i=K_{V_i}, then

    intersection_i E_i = K_{union_i V_i},
    E_i join E_j = K_{V_i intersection V_j}.

For the empty family the meet is the ACTUAL ambient Top, present in the
bounded exact lattice, and corresponds to the empty upset. Its quotient
is a singleton because X is nonempty. The abstract exact_crt theorem
for an arbitrary binary sublattice deliberately does not supply this
empty-family convention; the actual source instance does.

### Generic coloured quotient associativity (C03)

This helper works before exactness or any source hypothesis. Let G act on
X, and let K<=H be invariant equivalences. Give Q=X/K its complete canonical
G-pair-orbital language. The relation H/K is a union of these named pair
orbitals: a G-map preserves H and K. Every structural automorphism of Q
therefore preserves H/K and induces a permutation of its class set.

The map [[x]_K]_(H/K) -> [x]_H is well-defined, bijective and commutes
with the canonical quotient maps. It is also the intended COLOURED
identification, even if full Aut(Q) is larger than the original G-image.
Indeed, for each actual G-orbital Theta on (X/H)^2, its pullback to Q^2
is G-invariant and hence a union of the named Q pair orbitals. Full Aut(Q)
preserves that union, so it cannot mix two such coarse colours. Conversely
the original G-image is contained in Aut(Q) and is already transitive
inside each named coarse orbital. Thus the induced full Aut(Q)-pair
orbitals on its H/K quotient are EXACTLY the old coarse Theta colours.
No transitivity of X, finite language, homogeneity or global group lift is
needed for this generic calculation.

For the actual source, I03 applies to the saturated original exact H
and exact K: K;H;K=H, so H/K is full exact in Q's actual canonical
language. I02 then supplies standing-source status of each original exact
X_V. C03 identifies all iterated quotient languages and their intrinsic
finite-packet notions with the displayed actual X_W. All local owner
providers are invoked only AFTER this source/exactness step.

C05 and the finite product identities can instead be applied DIRECTLY to
original X with the two kernels K_Vminus,K_Up. This route needs no
countability or ordinary EPPA: the actual coarse colours recover the fine
K_V colour by the existing equality-inclusive exact colour-meet theorem.
At the end X_P=X/Id is canonically isomorphic to X; a receiving project
transports the finite set through that isomorphism instead of asserting
literal equality between quotient and original carrier types.

## N06: Every original shadow and one valid local provider

At a processed upset U retain, for EVERY upset V subset U:

- a finite nonempty actual induced B_V subset X_V containing A_V;
- for EVERY W subset V, restriction of the actual projection maps B_V ONTO B_W;
- all these maps commute and equal the displayed ambient canonical projections;
- M1–M4 for the subsystem, and recognition of every quotient kernel and pair
  colour as fine-colour unions on each finite B_V.

Surjectivity/commutativity should be stated explicitly in a formalization;
“constructed compatibly” in the article is intended to include them. They are
not inferred from M3, since an automorphism group map alone does not say a
carrier projection is onto.

For every new V the equivalence identities are
k_(Vminus) meet k_(U_p)=k_V and
k_(Vminus) join k_(U_p)=k_O.
The actual set-product and fine-colour providers identify
X_V = X_(Vminus) times_(X_O) X_(U_p), with its actual fine colours.

Apply the local owner provider to Q=X_(U_p) -> X_O and input A_(U_p).
Its owner base B_O is finite, nonempty, packet-closed by the old invariant.
A_(U_p) lies over A_O subset B_O. EPPA(Q) is the master's explicit hypothesis.
Obtain D_p with image exactly B_O and full finite-packet closure. Define each
new B_V as the FULL actual induced product B_(Vminus) times_(B_O) D_p.
For V=U_p this product is canonically D_p, since B_(Vminus)=B_O and the first
map is identity.

A_V maps injectively into that product by its canonical actual coordinates;
those coordinates are exactly A_(Vminus) and A_(U_p), which the factors contain.
Thus every original A_V, not just A or a chosen representative copy, is retained.

Let L=B_U times_(B_O) D_p=B_(U'). It maps onto every old B_T by its onto first
factor projection and the old B_U -> B_T. It maps onto every new B_V by
(b,x) -> (b|_(Vminus),x): a target (t,x) lifts by any b above t, whose O-owner
is correct because O subset Vminus. These maps commute with every ambient
projection. This proves the stronger compatible-system invariant. In particular
at the end pi_V(B_P)=B_V for EVERY V, which identifies the constructed system
with the quotient images asserted in the theorem statement.

C22 discharges the callback at each p with I04 on Q=X_Up->X_O.
Ordinary EPPA(Q) is exactly one of A07's original exact-quotient inputs.
The two input images of each sparse A_V are exactly A_Vminus and A_Up;
this follows by commutation and surjectivity of pi_V restricted to A.
The finite full product contains A_V pointwise in its actual ambient sort.
The principal product B_O times_(B_O)D_p is canonically D_p: the first
coordinate is forced to equal the owner of the second.

## N07: Full finite packets, with full quotient-group invariance

Fix a new V and either coordinate projection q:X_V -> Y, with kernel K.
Let F=F_(X_V). Both F and K are invariant equivalences in the symmetric
one-sort source, so they commute and F join K=F;K. Define
R=(F join K)/K on Y. For each w in X_V,
R[q(w)] = q(F[w]): one inclusion is direct and the reverse follows by writing
a (F;K)-witness. Therefore R has finite classes.

Its invariance under FULL Aut(Y) must be justified: F join K is K-saturated
and a union of fine orbitals of X_V. It descends to a union of the named
canonical Y pair orbitals. Every structural automorphism of Y preserves that
union, hence R <= F_Y. No arbitrary Aut(Y)-element was lifted globally.

If w in B_V and w' F w, the two images of w' lie in the corresponding
F-packets of its factor images. Old M2 and D_p's packet closure put those
images in B_(Vminus) and D_p. Since w' is an actual real X_V point, its
coordinates agree over X_O; this owner lies in B_O. FULLNESS of the finite
product puts w' in B_V. F need not be exact and no acl identification is used.

This is precisely the already expanded owner_action C06–C07/N03 support
proof (I07), not a second foundational proof export. The generic packet
transfer C15 merely needs its projection-respects-packets premise A09;
C25 supplies that premise from I07 in the actual symmetric framework.
The greatest finite packet F is not assumed exact. Neither side uses an
algebraic-closure identification or independently chosen fibre motions.

## N08: Full automorphism groups and every nested target

First apply the fine-coloured full-product group theorem separately to EVERY
new B_V. Coordinate maps are onto B_O by the invariant, and the coordinate
kernels are actual full exact kernels by descent. Thus
Aut(B_V)=Aut(B_(Vminus)) times_(Aut(B_O)) Aut(D_p).
These are full automorphism groups of the actual induced finite structures,
not selected subgroups of ambient restrictions and not only the motions chosen
in constructing D_p.

For largest L take D=B_U, C=D_p, common owner B_O.

Old target T=B_V: old M3 gives Aut(B_U) -> Aut(T) onto with fibre-transitive
kernel. The prescribed-owner point property of C is exactly the second-factor
input. The nonnested target branch applies even if V does not contain O.
One must not insert a fictitious map T -> B_O.

New target B_V: take T=B_(Vminus). Since O subset Vminus, B_U -> B_O factors
through T. The target W_T=T times_(B_O) D_p is exactly B_V, and its own group
identity was proved above. Old M3 supplies the first-factor input. The nested
product target branch gives onto Aut(L) -> Aut(B_V) and fibre-transitive kernel.
This also covers V=U' (identity map) and V=U_p (target D_p).

All full Aut(L)-elements descend to every B_V: recognizable actual coordinate
kernels make the induced permutation well-defined; recognizable quotient pair
colours make it a structural automorphism. Carrier surjectivity makes the
induced permutation unique. These facts also make all induced group maps
commute.

For any nested pair Vprime subset V, prove onto Aut(B_V) -> Aut(B_Vprime)
by lifting a target automorphism to Aut(L), then descending to B_V. Given
b,b' in B_V over the same B_Vprime point, choose lifts l,l' in L. Their
B_Vprime-images coincide. The kernel of Aut(L) -> Aut(B_Vprime) moves l to
l'; its descended automorphism of B_V fixes EVERY B_Vprime point, because the
quotient group maps commute and B_V -> B_Vprime is onto. It sends b to b'.
Thus M3 holds for every nested pair, not only maps with source L.

### Generic largest-cover action descent (C17)

Let L->Y->Z be onto maps, equivariant for group maps
G_L->G_Y->G_Z whose triangle commutes. Assume G_L->G_Z is onto and
its kernel is transitive on each L->Z fibre. Then G_Y->G_Z is onto:
lift any target group element to G_L and take its G_Y image. For y,y'
over the same z, choose any l,l' above them. Coherence makes their
Z-images equal; take a G_L-kernel element moving l to l' and descend
it to G_Y. Its G_Z component is identity and it sends y to y'.

This proof does NOT require G_L->G_Y onto, nonempty carriers, finite
sets/groups, faithful actions, exactness or EPPA. Empty Y makes its
point condition vacuous; group surjectivity follows from the explicitly
given G_L->G_Z surjectivity. In the source application the diagram maps
and homomorphisms are the actual recognizable finite quotient maps.

The local branches have separate premises: C18 uses old M3 plus D_p's
prescribed owner point property; C19 needs old M3, factorization and the
target's own product identity, but no D_p point property. The independent
EPPA clause in N09 needs neither point-kernel premise. Its sparse-input
containment and exact shadows are explicit conditional data in A14; C11
discharges them for every actual source input.

## N09: Every sparse source partial map and ordinary EPPA

Fix new V, W=B_V, D=B_(Vminus), C=D_p, common owner B_O.
A_W is the ACTUAL induced subset A_V, potentially sparse in the full product.
Its two entire coordinate images are exactly A_(Vminus), A_(U_p).

For any partial automorphism f:S -> S' of A_V, each coordinate partial map
has domain equal to the projected S, not necessarily the whole projected
input. Equality of coordinates is recognizable by fine colours, so coordinate
maps are well-defined and injective. Pullbacks of quotient pair colours are
also recognizable, so the maps preserve the actual quotient colours and are
genuine partial automorphisms of the respective A-projections. Keeping the
equality-inclusive language handles repeated coordinate values correctly.

Old M1 extends f_D to g in FULL Aut(D). Its actual B_O action is one definite
permutation delta. For each point in the projected domain of f_C choose an
S-lift; compatibility of the two original coordinates shows that delta agrees
with f_C on its old owners. Local provider clause (1), whose input was exactly
A_(U_p), extends f_C to h in FULL Aut(C) inducing precisely delta. The
matching pair (g,h) is a W-automorphism and extends f. This is the independent
EPPA clause of 03; its proof needs no point-kernel condition and no owner-group
section. Taking T=D in the article makes condition (i) tautological if one
uses the combined lemma's full statement.

Every f of A_V is covered, including partial maps which do not lift to a
partial map of original A. No enumeration of just projections of original
A-partial maps would suffice. Old witnesses are unchanged, so all old M1 remains.

## N10: Finite recursion, exact final image and source phase

The M4 upset form uses unions as the fine index and pairwise intersections
as common coarser owners. It includes repeated indices. For a family with no
p-containing member use old M4. Otherwise every p-containing member contains
U_p, and agreement on any two such members' intersection forces exactly one
shared D_p-coordinate x. Delete p from all indices and use old M4 on ALL old
coordinates, including the members which never contained p. This yields one
old b. From any p-containing member, b and x have equal B_O owner. Hence
(b,x) lies in the full new product and realizes the family. Both coordinates
are uniquely determined. A singleton family is immediate by the same argument.
The empty family is the singleton X_empty/ B_empty case, using actual ambient
Top rather than a generic sublattice maximum. Complementing back gives the
meet/join form in the theorem.

Only |P| principal-factor owner-provider calls occur; each uses a finite
request family and a finite ordinary EPPA construction. The number and sizes
of requests may grow, but the process is finite. There is no iteration until
stability and no use of a rooted/safe-palette hypothesis.

`unified_induction.tex` explicitly orders P_n < O_n < U_n. The local master is
U_n and may invoke ordinary EPPA of X itself: a principal upset U_p can equal
P. For example when P has a least element p, U_p=P, so its local source is
X_(U_p)=X. Therefore omitting E=Id from the master's input would create a
real missing premise; the article already includes it.

At U_n, O_n is available and strict quotient EPPA comes from lower ranks.
This is the stated noncircular use. Invoking U_n inside P_n, or deriving EPPA(X)
from this conditional master before O_n, would be circular. The local audit
verifies the master interface only; it does not establish that every global
rooted consumer meets its own named closure, safe-selector, reservoir and
decoder hypotheses. The source itself marks the global theorem as a
source-relative candidate proof, and that qualification must remain.

The abstract recursion C23 is a PRESERVATION theorem from a supplied
decorated singleton base (A17), not a source existence theorem from a bare
set singleton. At each stage it preserves finite nonempty sets,
coherent onto maps, all-family CRT and the supplied decorations. The actual
source instance C25 discharges its local inputs with C22/I04, group identities
with C16/I05 and packet preservation with I07. It uses exactly one local
owner-provider invocation per p (zero when P is empty); this is a finite
number of ordinary EPPA witness calls, not a uniform size bound.

Finally q_(P,V)(B_P)=B_V is a CONSEQUENCE of carrier surjectivity, not a
notation for independently selected finite witnesses. Transport B_P from
X/Id into X, then identify each exact quotient image canonically. Thus
the resulting single finite actual B satisfies all four source clauses.
The empty-family exact meet is ambient Top, whose quotient is one point.

The DAG records proof dependencies, not a demand to prove unrelated branches
in that order. In particular generic diagrams and the group descent helper
do not depend on CCO/ordinary EPPA; they are reusable conditional lemmas.
Only the actual source assembly imports the global exact geometry and the
countable provider route. The source-relative rooted/global candidate and
its consumers are not claimed proved by this module.

## N11: Independent finite controls and their exact limits

The executable `tools/check_owner_master_controls.py` enumerates all labelled
posets on zero through four points: 1,1,3,19,219, and all 1,008 descending
addition orders. It builds both full F2-coordinate diagrams and diagrams
with owner-dependent one/two-point local fibres. It checks canonical maps,
coherence, onto images, unchanged old objects and full binary squares.

Compatible tuples are computed INDEPENDENTLY by relational joins of their
own factor sets, then compared with the proposed union-space image. Exact
immutable join signatures are memoized, not a proposed answer. Every distinct
upset family is checked, including empty; one repeated member of every
nonempty family is tested as well. This is finite diagnostic coverage, not
the proof of arbitrary family length in C14. Complete counts are printed
by the script, including raw and distinct cache cases.

Actual all-difference structures separately enumerate their colour-preserving
permutations from all anchor images and test full quotient group homomorphisms,
onto images, every fibre kernel and prescribed point motion. The context-
dependent model is only a set-diagram test and is NOT asserted to satisfy
M3, packet closure or ordinary EPPA. A nonnested old-target example explicitly
has no T->O factorization.

Sparse parity shadows have all singleton/pair marginals but omit global
compatible tuples; a missing-corner pullback still has onto factor maps and
fails binary CRT. A two-point empty object fails empty-family bijectivity.
These examples deliberately violate master premises and are not source CCO
counterexamples. Neither control model certifies external ordinary EPPA,
actual exactness, source homogeneity or the infinite provider theorem.

An independent second audit also tested 51 naturally labelled transitive
posets through four points (covering all unlabelled shapes), all 285 valid
orders, and 126,746 bounded CRT families including 844,679 compatible tuples.
Its n=4 family enumeration was bounded in arity; the repository executable
provides the stronger all-distinct-family coverage. The mathematical N04
argument, rather than either finite experiment, proves all finite families.

## N12: Receiving package and human-article return

B020 is one substantial several-page package C01–C26, with internal T-tasks.
It reuses B008 exact CRT/descent, B018 finite owner providers and B019
fine-product/action contracts. No dependency on finite-kernel width-two,
phase seeds, SAP/NR2 selectors, Ramsey or a rooted ACF theorem is introduced.

This is a PRIVATE preparation package until a coordinated public catalogue/
STATE promotion. The current public workers keep their live allocations;
adding a package only to one side would fail the exact registry/state check.
Do not overwrite public BOARD, AUTONOMY, reports or STATE with the legacy
PREPARATION template. A future release must update the catalogue and ledger
consistently, without changing accepted source assumptions or worker claims.

The feedback ledger asks the human text to make exact double-quotient
imports, coherent onto carriers, sparse input containment, all-family
uniqueness and full finite-group descent explicit. No numbered conclusion
or human TeX is changed. The next source preparation is joint-owner point
homogeneity and the rooted/rank consumers, retaining their source-relative
candidate qualifications.
