# Real closure, SAP monolith and terminal incidence — proof notes

Source pin `490c3f36d85db5a0b3ced0598e6c431825254ec5`. Preparation for other formalization projects; no Lean proof is claimed. The human TeX is unchanged. The precise node contracts, source coverage, assumptions and dependency firewalls are in `module.json`. Source theorem exports retain their stated hypotheses; individual proof claims isolate weaker premises where valid.

## N00: Fixed named sort and ambient-action scope

The one-sort article is a special case of the fixed-sort contract used for
the selected typed terminal exports. In a possibly many-sorted original
source fix one inhabited named sort a and G=Aut of the WHOLE source. All
relations, equivalences, orbits and finite bases in the module are on that
sort, with G acting on it. In particular the full invariant lattice means
the G-invariant lattice on a, not an unproved identification of ambient
and reduct automorphism groups.

For a provider originally stated for a one-sort source, take the induced
complete same-sort binary structure N on a. Every finite partial isomorphism
of N extends to an ambient automorphism by original homogeneity. Consequently
G and Aut(N) have the SAME orbits on each finite tuple, including pairs and
tuples with a fixed finite base. Thus invariant binary equivalences and
finite-base point orbits coincide. Actual same-sort colours and represented
word products coincide literally. AP, SAP when assumed, and semantic
homomorphic CCO restrict to single-sort diagrams: any produced finite
amalgam can be restricted to the images of the pure-a factors, and a
sort-preserving homomorphism of such a diagram lands in a. These facts
justify the one-sort hull, class and exact-lattice provider instances.
They do not assert that every full automorphism of N extends ambiently.
Terminal word presentations can alternatively be proved directly with G,
as N08 does, from its finite actual pair-orbital palette and transitivity.

## N01: Elementary lattice, finite joins and minimal infinite exactness

Work on the actual inhabited transitive homogeneous original real source,
with its finite complete symmetric binary orbital language, AP, semantic
homomorphic CCO, and the original triangle-fullness law already isolated as
`lem:cco-triangle-fullness`. All products are represented. Invariant binary
relations commute because they and their products are symmetric. Consequently
the join of invariant equivalences is their product. The full invariant
equivalence lattice is finite, since every relation is a union of finitely
many original atoms. Its distributivity is neither assumed nor asserted.

The join of two finite-class invariant equivalences E,H has finite classes:
for a fixed x, (E;H)[x] is a union of the finitely many H-classes reached
from points of E[x]. Transitivity makes each class size uniform, and gives
the optional bound |(E join H)[x]| <= |E[x]| |H[x]|. Induction handles
finite joins. Thus the join F of ALL finite-class original invariant
equivalences exists and has finite classes; the family includes Id. Every
finite-class original invariant equivalence lies below F. This establishes
the needed meaning of Sigma(Id) locally, without constructing Sigma(J),
packet cores or arbitrary finite-index closures. If M is finite, F=Top.
If M is infinite, F is proper and its nonempty classes still have one
constant finite size. Do not assume F is RAW word-exact.

List all inclusion-minimal infinite-class original invariant equivalences
as E_1,...,E_r. Distinct entries are incomparable. Every proper invariant
equivalence below an E_i has finite classes, by minimality. Every infinite
invariant equivalence contains an E_i, by finite-poset minimal selection.
When M is finite the list is empty and r=0; when M is infinite Top is
infinite-class, so r>=1. These are original equivalences, not arbitrary
imaginary kernels.

Only the exactness clause of `prop:minimalcut` is needed, and it has the
following direct proof. An infinite E_i-class contains a finite triangle
Ramsey configuration for the finite original palette. Here is an elementary sufficient bound: for k>=1 put f_k(0)=1 and f_k(t+1)=k*f_k(t)+1. From f_k(k+1) vertices, repeatedly choose a pivot and a largest monochromatic neighbour set for the remaining stages. This gives k+1 pivots with assigned outgoing colours and a final vertex. Two pivot colours agree; those two pivots and a later vertex form a monochromatic triangle. An infinite class contains this finite configuration; its diversity palette has k>=1. Hence it contains a
monochromatic triangle, in an actual diversity atom a below E_i. This a is
looped. For every integer m, the complete a-coloured graph on m distinct
points is legal by triangle fullness. All its points lie in one Gamma(a)
class. Align one of its vertices to any fixed original point by transitivity;
the Gamma(a)-class of that fixed point therefore has at least m points.
Thus Gamma(a) has infinite classes. Since Gamma(a)<=E_i, minimality gives
Gamma(a)=E_i.

The positive even-word expansion of `lem:rh-evenwalk` makes B(a)^+ a
stabilized positive even power of a. As a is looped, a belongs to A_a and
hence to B(a), while A_a is contained in Gamma(a). Therefore B(a)=Gamma(a).
Thus every E_i is an actual positive atomic word profile, in particular
FULL RAW exact. This uses finite Ramsey and triangle fullness plus the
elementary even-walk argument; it imports neither the full packet-interval
theorem nor the quotient-source conclusion of `prop:minimalcut`.

Now use the prepared `lem:acf-exact-distributive` contract: original FULL
RAW exact equivalences form a finite bounded distributive sublattice, with
ambient meets and represented-product joins. Define K_fin as the join in
that sublattice of all its finite-class equivalences, including Id. The
finite-join observation makes K_fin finite-class, and K_fin<=F. Equality
need not hold. K_fin and the E_i are FULL RAW exact; F is only an original
finite-class invariant equivalence. Every meet of exact equivalences here
contains Id, so the nonempty-result guard on exact meet closure is satisfied.

## N02: Boolean directions and CRT avoidance

Put A_i=K_fin join E_i and A_S=K_fin join (join_(i in S) E_i), with
A_empty=K_fin. All these equivalences are FULL RAW exact. For distinct
i,j, E_i meet E_j is properly below E_i and therefore finite-class.
It is exact as a meet of exact equivalences, so it lies below K_fin.
Distributivity in the EXACT sublattice gives

    A_i meet A_j = K_fin,
    A_S meet A_T = A_(S intersect T),
    A_S join A_T = A_(S union T).

The join identity follows directly from the definitions; the meet identity
uses finite distributivity and the pairwise intersection calculation. Empty
subsets use the stated K_fin convention. No distributivity of the full
original invariant lattice is used. Each A_i has infinite classes because
it contains E_i.

Fix a nonempty S and i in S, and write T_i=A_(S minus {i}). Then
A_i meet T_i=K_fin. In one infinite A_i-class, the intersection with any
T_i-class, if nonempty, is exactly a K_fin-class. It is therefore finite.
Consequently that A_i-class meets infinitely many T_i-classes, so
[A_S:T_i] is infinite. This argument includes |S|=1, when T_i=K_fin.

The witness selection below replaces the human source's subgroup/Neumann
route. Its only Helly input is the prepared different-centre exact-ball
statement `lem:exact-balls`, equivalently exact class Helly in the prepared
CRT module. It is NOT Helly merely for binary support intersections.

Fix one original point x and C=[x]_(A_S). Choose i0 in S. For i0 choose a
T_i0-class D_i0 inside C which meets none of the finite set F[x]. There are
only finitely many forbidden T_i0-classes (at most |F[x]|) and infinitely
many available classes inside C. Since x belongs to F[x], this also excludes
T_i0[x]. For each remaining i choose a T_i-class D_i inside C different
from T_i[x]. These choices are possible by the preceding infinite-index
calculation. Each D_i is an actual nonempty class, not a formal colour menu.

If i!=j, then (S minus {i}) union (S minus {j})=S, hence
T_i join T_j=A_S. Original equivalences commute, so T_i;T_j=A_S. Choose
representatives y_i in D_i and y_j in D_j. Both lie in C, and therefore
y_i A_S y_j. A represented product witness y_i T_i z T_j y_j shows
D_i intersect D_j is nonempty. The finitely many exact classes D_i thus
meet pairwise. Exact-ball/class Helly supplies y in their total intersection.
For |S|=1 pairwise compatibility is vacuous and any point in the one chosen
class suffices. S=empty is never subjected to this selection.

The chosen y avoids F[x] and every T_i[x]. Its actual old atom
t_S=col(x,y) is diversity, since x belongs to F[x], and lies outside F.
It belongs to A_S but to none of its facets T_i. Invariance/atomicity turn
each witnessed pair-membership or nonmembership into membership or
nonmembership of the entire original atom.

If S,T are distinct nonempty subsets, choose i in S minus T, reversing
their roles if necessary. Equality t_S=t_T would put that atom in
A_S meet A_T=A_(S intersect T)<=A_(S minus {i}), contradicting its
facet avoidance. Thus all 2^r-1 nonempty subsets give distinct original
diversity atoms outside F. It follows that
2^r-1<=|D outside F| and r<=floor(log_2(|D outside F|+1)). For r=0
there are no witnesses to select and the inequality is 0<=|D outside F|.
When |D outside F|=0, the bound forces r=0.

F enters this proof only through the finite forbidden POINT set F[x]. It
is not one of the exact balls to which Helly is applied, so no exactness
of F is required. The original source's Neumann finite-coset-cover argument
remains a valid alternative proof route, but this expansion uses neither
that theorem nor `lem:finite-action-avoidance`, group stabilizer indices or
coset actions. No Lean availability for any of those alternatives is claimed.

## N03: Algebraicity criterion and bounded character

For finite real A and x outside A, let p_a=col(x,a) and
J=intersect_(a in A) Gamma(p_a), with the empty intersection interpreted
as universal diversity support. The actual canonical class is

    [x]_(E_J) = intersect_(a in A) [a]_(E_Gamma(p_a)).

Indeed x and a already lie in the same Gamma(p_a)-class for each a.
Every automorphism fixing A preserves each literal spoke colour, so the
actual one-point orbit/fibre of x over A is contained in this canonical
class. The class need not equal that orbit. Gamma(p_a) is a full invariant
support and need not be RAW exact.

If x is algebraic over nonempty A, `thm:rh-hull` makes its canonical class
finite. Conversely, a finite canonical class contains the whole A-orbit
of x, so x is algebraic. For empty A, transitivity makes the orbit M and
the canonical class M; both are finite exactly when M is finite. Thus the
same equivalence holds with the empty-intersection convention. In this
homogeneous finite relational language, the complete one-point atomic type
over a finite real A is a finite formula defining precisely the orbit;
finite orbit agrees with real model-theoretic algebraicity.

By N01 and finiteness of the full original equivalence lattice, E_J has
infinite classes iff some E_i<=E_J. Negating the inclusion into the finite
meet gives, for x outside A,

    x in acl(A) iff for every i<=r there is a in A with
                         E_i not <= E_Gamma(col(x,a)).

When r=0 the source is finite and this is vacuous, as required. For an
infinite source r>=1, and with A empty the right side fails, agreeing with
acl(empty)=empty. This criterion uses the canonical hull, not an assertion
that the original one-point fibre equals the canonical class.

For an algebraic x outside A choose one witness a_i in A for each i and
let B be their set. Then |B|<=r, B<=A, and the same criterion shows
x in acl(B). If x belongs to A and M is infinite, r>=1 and B={x} works.
If M is finite, all points are algebraic over empty. Monotonicity supplies
the reverse inclusion, yielding

    acl(A) = union_(B subset A, |B|<=r) acl(B).

This finite-family witness argument itself needs no palette-cost theorem;
N02 adds the sharper logarithmic bound on r. Neither direction invokes
SAP, algebraicity in arbitrary imaginary sorts, or a quotient-word descent
statement.

For one parameter a and x!=a, the criterion says that Gamma(col(x,a)) has
finite classes. By maximality of F this is equivalent to Gamma(col(x,a))<=F,
which in turn is equivalent to col(x,a)<=F, since F is an equivalence.
Hence acl({a})=F[a], including a itself. If r=1, bounded character therefore
gives acl(A)=F[A] for every finite real A, with F[A] the union of the
F-classes meeting A. Here the source is infinite, so the empty case on both
sides is empty. This does not establish harmlessness of owner imaginaries.

## N04: Polynomial bound, packets and definability

Assume now M is infinite. Then r>=1, d_infinity=|D outside F|>=1 and
acl(empty)=empty. Let f be the number of original diversity atoms inside F,
and let c be the positive finite size of an F-class. Original transitivity
makes c constant. Apply `cor:rh-class-2power` to the original finite-class
equivalence F, without assuming it word-exact: c=2^m<=2^f.

Every realised FINITE one-point fibre Z over a nonempty finite complete
real base is one class of an original invariant equivalence K by
`thm:rh-globalise`. Because one K-class is finite and the original source
is transitive, every K-class is finite. Hence K<=F and |Z|<=c. This is
globalisation of the actual fibre, not identification with the potentially
larger canonical hull. The source phrase "exact for Z" means fibre-closed
whole-class containment, not FULL RAW word-exactness of K.

Let A have size n. The set F[A] has at most cn points. For any
x in acl(A) outside F[A], N03 gives a nonempty B subset A of size
j<=min(r,n) with x in acl(B). B cannot be empty because the source is
infinite. Also x is outside B. Every spoke col(x,b), b in B, lies outside
F, since otherwise x would belong to F[b]<=F[A].

For fixed B of size j, at most d_infinity^j tuples of outside-F spoke
colours are possible. Some tuples may be unrealised; counting all tuples
is only an upper bound. Homogeneity identifies each realised complete
spoke type with one orbit. The algebraic types are exactly those with
finite fibres, each of size at most c by the preceding globalisation
argument. Distinct types over the SAME B have disjoint fibres. Thus at
most c d_infinity^j such points are algebraic over B outside F[A].
Taking a union over all B, without asserting disjointness between different
bases, yields

    |acl(A)| <= c (n + sum_(j=1)^min(r,n) binom(n,j) d_infinity^j).

For n=0 the sum and F[A] are empty, agreeing with acl(empty)=empty. For
n>=1, r>=1 makes the linear term O(n^r), and every term of the fixed
finite sum has degree at most r. Therefore |acl(A)|=O_M(n^r), with a
constant depending on the original source. The logarithmic restriction
on r is N02.

The closure is a union of COMPLETE F-classes. One can prove this without
importing transitivity of model-theoretic algebraicity: if x has finite
A-orbit and yFx, then every image of y under Aut(M/A) belongs to the
F-class of some image of x. There are only finitely many such classes,
each of size c, so y also has finite A-orbit. Thus acl(A) is F-saturated.
Its F-classes are pairwise disjoint and all have size c. Dividing the
cardinality bound by c gives at most
n+sum_(j=1)^min(r,n) binom(n,j)d_infinity^j complete packets.

If F=Id, every finite realised one-point fibre is a singleton. For an
algebraic x outside a finite A, its complete finite spoke formula over A
therefore has exactly one realisation and defines x. Parameters in A are
already definable by equality. The empty-base case has no algebraic point
in the infinite source. Hence acl(A)=dcl(A) for finite REAL A when F=Id.
This need not say acl(A)=A, and makes no claim about arbitrary imaginaries.

## N05: Coordinate sharpness source

For fixed r>=2 take M_r=Nat^r and name each nonempty difference support
S={i:x_i!=y_i} as a distinct symmetric diversity atom. Coordinate equality
in coordinate i is the union of equality and the atoms whose supports omit
i, so every automorphism preserves each coordinate equality individually.
It induces one permutation of Nat in each coordinate; conversely every
such product of coordinate permutations is an automorphism. A finite
partial isomorphism gives well-defined finite partial bijections on the
values in each coordinate, because it preserves coordinate equalities in
both directions. Extend these bijections to permutations of Nat. Their
product extends the given partial isomorphism, proving homogeneity.

Every triangle-legal complete finite diagram gives an equivalence relation
of coordinate equality for each i. Assign different Nat values to its
finitely many classes, independently for each coordinate. Nonempty
diversity supports ensure that distinct formal vertices get distinct
tuples. This realises the diagram and proves triangle fullness. The actual
age has AP by aligning finite common substructures using homogeneity and
taking a finite induced union; identifications outside the base are allowed.

For semantic homomorphic CCO, read each specified colour as coordinate
equalities and disequalities. An inconsistent coordinate specification has
one disequality edge whose endpoints are connected by equality edges in
that coordinate. A shortest equality path is simple, has length at least
two, and together with that edge is a specified simple cycle without a
homomorphism. Conversely, if every specified simple cycle maps, no such
obstruction exists. In each coordinate assign distinct values to its
equality components. This satisfies all specified edges simultaneously.
Unspecified vertices may be identified, as allowed for homomorphic CCO.

The full invariant equivalences are precisely the coordinate-change
equivalences E_I, I subset [r]. To verify completeness of this list, let
an invariant equivalence contain an atom of difference support S. For any
i in S, realise two consecutive edges of that SAME atom with endpoints
differing only in coordinate i: choose a fresh third intermediate value in
coordinate i, another value for the intermediate point in each coordinate
of S minus {i}, and keep all other coordinates constant. Both edges have
support S. Transitivity therefore forces the singleton support {i} into
the equivalence. Single-coordinate steps generate E_I for the union I of
all supports present. No other supports occur by the definition of I, so
the equivalence equals E_I.

Every nonempty I gives infinite E_I-classes; hence F=Id. The r singleton
coordinate-change equivalences are exactly the minimal infinite ones, and
there are 2^r-1 original diversity atoms. Thus the exponential palette bound
is attained with equality as well.

More generally, for a finite A let V_i be its finite set of i-th coordinate
values. Its pointwise stabilizer fixes every value in each V_i. A tuple
whose coordinates all belong to the respective V_i is fixed. If a tuple
has a coordinate outside V_i, permutations of Nat fixing V_i give it
infinitely many images. Consequently

    acl(A)=dcl(A)=product_i V_i.

For the diagonal A_n={(k,...,k):1<=k<=n}, this gives [n]^r, of cardinality
n^r. For n=0 both sides are empty; for n=1 the closure is the parameter
itself. For r>=2,n>=2 the grid strictly contains the diagonal. Thus the
polynomial exponent r is sharp even for real definable closure, without
assuming SAP or invoking a classification theorem.

For r>=2 this source fails SAP directly: the off-base point (0,0,0,...,0) is uniquely specified over (0,1,0,...,0) and (1,0,0,...,0) by its two complete spoke colours. Two copies of that extension over the same complete anchor cannot have distinct new points in any age amalgam. This is independent of the abstract SAP-orbit theorem.

## N06: SAP orbit duplication and invariant monolith

Source pin: `490c3f36d85db5a0b3ced0598e6c431825254ec5`. These are human-expanded mathematical proof notes, not Lean proofs. The source is `real_hull/07`, beginning with `lem:rh-sap-invariant-monolith`.

For this branch take an infinite inhabited transitive ultrahomogeneous structure in a finite complete original binary language, whose actual finite age has SAP. Symmetry, CCO, triangle fullness, exactness and lattice distributivity are unnecessary. Completeness and homogeneity identify invariant binary relations with unions of finitely many actual pair orbitals. In particular, finite induced embeddings preserve the original invariant equivalences used below. In a nonsymmetric language these are ordered pair orbitals; do not import the symmetric RAW commutation law.

First prove the reusable SAP duplication lemma. Fix an actual finite complete real base A and u outside A. Repeatedly strongly amalgamate copies of the complete extension A subset A union {u} over the same labelled A. For every positive integer n the age contains an extension with n distinct new points, each having exactly the original complete quantifier-free one-point type over A. Embed that finite extension into M. Its copy of A need not initially be the prescribed actual A: postcompose with an ambient automorphism aligning its labelled anchor to A, using homogeneity. The resulting n distinct points lie in the actual fibre of u over the fixed A. Homogeneity over A makes that fibre a single stabilizer orbit, so its size is at least every finite n and is infinite. Empty A is permitted. This argument proves acl_M(A)=A for every finite real A: an off-base algebraic point would have a finite stabilizer orbit. The complete one-point fibre is also definable by its finitely many original formulas, if the converse finite-orbit criterion is needed. No imaginary orbit statement is included.

Now let E,F be original invariant equivalences strictly above real identity. For a fixed actual x, transitivity supplies y!=x with xEy and z!=x with xFz. It is possible that y=z; the anchor A={y,z} then has one point. In either case x is outside A. Apply the duplication lemma to the complete type of x over this fixed A. Every resulting point x_i satisfies x_i E y and x_i F z, because its actual pair types to the anchors are unchanged. Since x E y and x F z, all x_i lie in the SAME actual (E intersect F)-class of x. Thus this particular class is infinite. The same construction works at every x; alternatively original transitivity makes all classes conjugate. This anchor alignment avoids the invalid general inference that unbounded finite classes in unrelated locations automatically yield an infinite class.

There are only finitely many invariant equivalences. The family of nonidentity ones is nonempty because Top>Id on an infinite set. Binary intersections of members remain nonidentity and have infinite classes by the preceding argument, allowing E=F. Its finite total meet L therefore remains nonidentity and has infinite classes. It is the unique least nonidentity invariant equivalence. Every nonidentity equivalence has infinite classes, so the greatest finite-class equivalence is Id. The unique minimal infinite direction is L; it may equal Top, exactly in the primitive case. The assertion r=1 is a translation of this conclusion into the notation of the earlier palette-cost section, not an import from that section.

Only duplication over bases of at most two points is needed for the common-monolith part. Trivial algebraic closure over arbitrary finite bases uses the corresponding full finite-base SAP duplication property. The existing `strong_selectors` SAP orbit-infinitude proof has the same elementary mechanism, but its symmetric typed source assumptions must not be silently inherited by this nonsymmetric branch. Either reuse a suitably generalized elementary contract or give the argument above.

## N07: Finite full-lattice MI reconstruction and realised tuple fibres

This expands `cor:rh-sap-mi-joint-real-fibre`. First separate an order-theoretic lemma valid in EVERY finite inhabited lattice, with its genuine greatest element Top. A proper meet-irreducible means J!=Top and J=A meet B implies J=A or J=B. Every X is the meet of all proper meet-irreducibles J>=X, with an empty meet equal to Top. No distributivity, commutation, group action or exactness is needed.

To prove it, fix Y not<=X. Choose a maximal J with X<=J and Y not<=J; the set is nonempty because X itself qualifies. Such J is proper because Y<=Top. If J=J_1 meet J_2 with both J_i>J, maximality gives Y<=J_1 and Y<=J_2, a contradiction. Thus J is proper meet-irreducible and separates Y from X. Let Q be the meet of all proper meet-irreducibles above X. Certainly X<=Q. If Q not<=X, use the separation just proved with Y=Q to find a member J of that family with Q not<=J, contradicting the definition of Q. For X=Top the family is empty and the formula is Top=Top.

This arbitrary-lattice reconstruction is NOT the distributive meet-primality/cofinality statement in `exact_crt`. The latter says a finite meet below a meet-irreducible has a selected factor below it, and requires distributivity. Do not import that stronger assumption or that different conclusion here. A dual finite irreducible-decomposition proof is another valid route, provided its nondistributive core is kept explicit.

Return to the full original invariant-equivalence lattice and its monolith L from N06. Every nonidentity element contains L. Hence the proper meet-irreducibles above L are exactly all proper NONIDENTITY meet-irreducibles of the full lattice, denoted I^times. Real identity is expressly excluded even though it is meet-irreducible in this monolithic lattice. N07's finite-lattice reconstruction yields meet_(J in I^times) J=L.

For an ACTUALLY REALISED tuple Phi(x)=([x]_J)_(J in I^times), an original real y has the same tuple precisely when xJy for every J, equivalently xLy. Its real fibre is therefore the full infinite class [x]_L. This kernel identity itself is elementary for any family of equivalences; MI is used only to identify its meet as L.

The pointwise stabilizer of the quotient tuple consists exactly of ambient automorphisms g with gx in [x]_L. By invariance of L this is also the setwise stabilizer of [x]_L. Conversely, preserving that L-class makes gx J-related to x for every J and hence fixes every quotient coordinate. For any y in [x]_L, ambient transitivity supplies g with gx=y; the preceding criterion puts g in the tuple stabilizer. Its orbit on x is exactly [x]_L and is infinite. No ambient automorphism section, extension theorem for quotient maps or CCO of an imaginary sort is used.

If I^times is empty, the finite-lattice formula gives L=Top. Since L is the least nonidentity element, the source is primitive. Phi is the empty tuple, its stabilizer is the whole ambient group and its only real fibre is M. This is a genuine empty-family case, not an implicit inclusion of identity among the coordinates. For an arbitrary, not necessarily realised tuple, N07 alone asserts no existence of a common real representative.

## N08: CCO-free terminal word presentation

This expands the selected result `lem:typed-all-invariant-equivalences-raw-word` in `terminal_invariant_raw_exact.tex`. Its second selected result, `lem:typed-terminal-all-equivalences-exact`, combines this word presentation with exact-ball Helly to obtain terminal full-lattice distributivity, as detailed in N09.

Use a homogeneous finite-complete binary source with finite old pair palettes and inhabited individually transitive named original sorts. Fix one original real sort a; require its same-sort orbitals to be symmetric. Assume its FULL original invariant-equivalence lattice has no relative-index-two interval. No SAP, CCO, triangle fullness, exact-ball Helly, distributivity, primitivity or visible/hidden quotient hypothesis is needed for the word argument. Every relation and word product remains the actual equality-inclusive RAW relation on original points. In particular, an empty word is actual Id_a, not a diversity colour.

For any invariant equivalence E on a, the case E=Id_a is the empty word. This also handles a singleton sort. Otherwise list the finitely many diversity orbitals t_1,...,t_m contained in E. For each t_i let F_i be connectedness in its actual undirected graph, including equality. It is an original invariant equivalence and F_i<=E. Transitivity makes the nonempty t_i relation serial at every point, so its graph has no isolated vertices.

If one t_i component were bipartite, transitivity would make all components bipartite: an ambient automorphism carrying a vertex to another carries its whole component and its graph structure. The even-walk relation Y_i, including zero-length walks, would then be an ORIGINAL invariant equivalence. Each connected component has exactly two nonempty parity classes, so [F_i:Y_i]=2. This is an interval in the full original invariant lattice and contradicts the hypothesis. It follows that every component is connected and nonbipartite. No CCO odd-cycle obstruction has been invoked here: nonbipartiteness follows instead from the exclusion of the original index-two interval.

In a connected undirected nonbipartite component, every ordered pair of vertices has walks of both parities. Start with a path between the pair; an accessible odd cycle and a return detour change parity, and two-edge backtracks preserve parity while increasing the length by two. Thus for each pair there are even and odd threshold lengths above which every length of the respective parity is realised. Equal endpoints are included: use the zero walk for one parity, an odd-cycle detour for the other, and seriality for positive even backtracks.

There are finitely many ORIGINAL ordered pair orbitals in F_i, including diagonal. Choose one representative pair and both parity walks for each orbital. By old pair homogeneity the resulting walks transport to every pair in that orbital. A single finite maximum of the even and odd thresholds gives N_i such that t_i^n=F_i for EVERY integer n>=N_i. The opposite inclusion follows because all t_i edges lie in F_i. Choose a positive n>=N_i to obtain one positive atomic word representing F_i. Finiteness of the old orbital palette is what makes the bound uniform even when components are infinite; mere pointwise eventual walk existence is insufficient without this step.

All original same-sort invariant relations commute: each is a union of symmetric orbitals, their actual product is invariant and hence symmetric, and converse reverses the factors. For invariant equivalences the product is their join. Therefore F_1;...;F_m is an equivalence below E which contains actual identity and every diversity atom of E, and hence equals E. Concatenate the positive atomic words representing the F_i. This represents E by ONE actual old atomic word. The empty list was already handled by E=Id_a. E is consequently full RAW exact under the original finite-intersection definition. No general assertion that a union of exact relations is exact is used.

The no-index-two premise is the FULL sortwise premise, not the corresponding assertion merely inside an exact sublattice. Connectedness Gamma(t_i) is not automatically word-exact in a general source; it becomes a word profile here because the forbidden parity interval forces nonbipartiteness. Ordinary powers need not stabilize when that premise is dropped. Nor does this CCO-free word result alone justify full-lattice distributivity: exact-ball Helly is still a separate CCO-dependent input.

## N09: Infinite exact Helly and terminal upgrade

For `cor:rh-sap-infinite-exact-helly`, restore the original infinite transitive homogeneous finite complete SYMMETRIC binary SAP source with semantic homomorphic CCO. Let E_1,...,E_m be nonidentity full RAW exact invariant equivalences on the same original sort and C_i actual classes. Suppose the classes intersect pairwise.

For m>=1, apply the original different-centre full exact-ball Helly contract to C_i=B_(E_i)(x_i). This is the precise nonemptiness provider; Helly of binary supports alone does not establish the assertion for balls with different centres. The RAW provider is `thm:full-typed-exact-balls`(iii), or its one-sort `lem:exact-balls` specialization. It does not itself require SAP. Once a point x in all C_i is obtained, equivalence-relation algebra gives C_i=[x]_(E_i) and intersect_i C_i=[x]_(meet_i E_i). This equality requires neither CCO nor commutation nor exactness after nonemptiness is known.

N06 now supplies the size conclusion. The finite meet of the nonidentity E_i contains the monolith and has infinite classes. Therefore the displayed common class is infinite. SAP supplies this infinitude; CCO plus RAW exactness supply a common real representative. MI plays no role in this arbitrary finite-family statement. For m=1, pairwise intersection is vacuous and the class is infinite by N06. For m=0, take the ambient meet Top and the intersection M; it is infinite. If one of the kernels is real identity, the infinite-size claim is not asserted: any nonempty intersection is then at most a singleton.

For the terminal upgrade assume full original sortwise NR2 as in N08. Every original invariant equivalence is then a full RAW atomic word profile, without needing SAP or CCO for that presentation. The same exact-ball Helly argument applies to arbitrary nonidentity original equivalence classes. In particular the finite exact lattice is now the FULL invariant lattice. Instantiate the exact-lattice/CRT branch of `exact_crt` to obtain full-lattice distributivity and finite compatibility CRT. Alternatively apply its abstract class-Helly-to-distributivity proof directly. This proves the second selected source result `lem:typed-terminal-all-equivalences-exact`; retain its source SAP+CCO hypotheses for the source export, while recording that SAP was not needed for the word stage or for distributivity once the CCO exact-ball provider is supplied.

The dependencies must flow from noNR2 to word presentations, then from exact-ball Helly to full-lattice distributivity. Never invoke distributivity to prove the word presentations. The `strong_selectors` eventual STRONG loop-power argument is not a substitute for N08: this route concerns original equality-inclusive RAW words, and has its own proof.

Apply the terminal upgrade to the finite family of all proper nonidentity full-lattice MI quotient classes. Define pairwise compatibility as actual pairwise intersection; in the symmetric source it is equivalently agreement in the pairwise join quotients, since invariant equivalences permute. Helly yields a common real point exactly when all pairs are compatible. The necessary direction is immediate. Once realised, N07 identifies the entire common real fibre with an infinite monolith class. In the primitive empty-coordinate case the empty tuple is realised by every real point, and the fibre is all of M. No infinite-family Helly, no surjectivity onto arbitrary tuples without compatibility, and no SAP of a hidden expansion naming additional non-MI exact quotient sorts is asserted.

The external prepared providers for N06–N09 are original RAW exact-ball Helly and, for terminal distributivity, the exact CRT instance or its abstract theorem. N06 itself proves the generic SAP duplication mechanism. This is the same reusable argument requested in B001; the receiver should reuse its accepted implementation when its hypotheses are general enough, and otherwise add the nonsymmetric elementary generalization here without retroactively enlarging B001. Canonical-hull finiteness, globalisation, Hasse/parity and the palette-cost bounds are not premises of these arguments. The identification F_fin=Id and r=1 is a direct SAP consequence, not a reverse use of a real-closure theorem.

## N10: Cartesian phase corners and nonexact packet

This audits `ex:two-coordinate` and `rem:phase-thin-not-exact`. Let M*=N times N times F2. For distinct points (r,c,g),(r',c',g'), the fine symmetric colour is (1_(r=r'),1_(c=c'),g+g'). All eight bit triples occur as pair types, but (1,1,0) is exclusively logical equality; the remaining seven are diversity atoms.

An automorphism consists of independent permutations of the two infinite coordinate sets and one common phase translation. Conversely a finite colour-preserving partial isomorphism preserves both coordinate-equality patterns and all pairwise phase differences. Its coordinate maps extend to permutations, and all represented phase changes agree with one common translation. This proves transitivity and ultrahomogeneity. The age has AP by homogeneity. It is not SAP, as the corner below gives an off-base uniquely definable real point (equivalently, two copies of that extension cannot be strongly amalgamated over their anchors).

For complete-diagram triangle fullness, legality forces each coordinate-equality relation to be an equivalence and the phase differences to satisfy the triangle cocycle law. Assign distinct coordinate values to the respective equivalence classes and integrate the phase differences. A distinct pair cannot receive the same full triple because its specified colour is a diversity atom rather than (1,1,0). Thus the resulting map is injective and is an induced embedding. Handle diagrams with at most two points directly.

For semantic homomorphic CCO on a finite partial diagram, treat the two coordinates separately. The equality edges of one coordinate generate connected components which must receive a common coordinate value. A specified inequality whose endpoints are in one such component gives that inequality edge plus a shortest equality path; these form a specified simple cycle with no homomorphism. The path has length at least two because a single specified edge cannot impose both equality and inequality in the same coordinate. If no such obstruction exists, assign distinct natural numbers to distinct equality components, separately in the two coordinates.

For the F2-differences, integrate gains along a spanning forest. Inconsistency gives a closed walk with nonzero total gain; decomposing it into simple cycles yields a specified simple cycle with nonzero total gain and hence no homomorphism. If all specified simple cycles complete, the gain system is consistent. Choose one additive constant in each specified-edge component and integrate. Combine these phase values with the two solved coordinate systems. Every specified edge retains its exact two equality/inequality bits and its phase difference. Its endpoints cannot coalesce, since an edge with both coordinate bits equal to one necessarily has phase difference one. Unspecified pairs may coalesce, which is allowed. This gives one simultaneous colour-preserving homomorphism and proves semantic CCO, not merely triangle fullness or AP.

The greatest finite-class invariant equivalence F has the two-point packets {(r,c,0),(r,c,1)}. This is an invariant equivalence. Any colour outside its thin flip changes at least one infinite coordinate and has infinitely many neighbours from each point; therefore an invariant equivalence containing that colour has infinite classes. Thus no larger finite-class invariant equivalence exists. The global phase translation acts freely and transitively on each packet, explaining the regular thin description.

Take a=(0,1,0), b=(1,0,0), x=(0,0,0). The two colours (1,0,0) from x to a and (0,1,0) from x to b fix respectively its row/phase and column/phase. Together they determine x uniquely, so x lies in dcl({a,b}). Its row/column pair is neither anchor's pair, hence x is not in F[{a,b}]. This is a concrete algebraic corner outside packet closure.

For the atom p=(1,0,0), its graph on each fixed row/phase is an infinite clique. Thus p squared is precisely the equivalence 'same row and phase', including actual identity; it is a full RAW exact word profile and is also the connectivity equivalence generated by p. Likewise the atom q=(0,1,0) has q squared equal to 'same column and phase'. These two infinite exact equivalences intersect in actual equality. Their indicated anchor classes intersect in {x}, exactly the singleton canonical hull in this example. General connectivity is not being declared exact; the explicit square computation establishes exactness here.

Every original diversity atom has one fixed phase difference, and actual identity has difference zero. Any finite atomic word, including the empty word, therefore has one fixed endpoint phase difference, the F2-sum of its letters. Any nonempty finite intersection containing a word restriction has that same fixed phase difference. The empty restriction list gives Top, which has both phase differences. The proper finite-packet equivalence F contains identity of phase zero and the flip atom of phase one, so it cannot be full RAW exact. The same argument excludes the proper equivalences 'same row irrespective of phase' and 'same column irrespective of phase'. Parameter-free invariance, finite classes, thinness and regularity therefore do not imply word-exactness. This example is AP+CCO and non-SAP, and so contradicts none of N06--N09's SAP infinitude assertions. It also does not address owner-relative closure after additional imaginaries are named.
