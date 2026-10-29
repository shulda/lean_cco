# Named owners, anchored completion and the residual transversal

Source pin: `490c3f36d85db5a0b3ced0598e6c431825254ec5`. These are human
proof specifications for OTHER Lean projects, not Lean declarations or a
new representation theorem. They expand all twelve selected source exports.
The source TeX remains authoritative; no source or Lean changes are made.

## N01: Scope, source exports and imported contracts

The twelve exports, including the entire named results rather than only
their eventual consumer-facing clauses, are as follows.

| Export | Actual source label | Expansion |
| --- | --- | --- |
| OT01 | `lem:anchored-closed-walk` | N02 |
| OT02 | `thm:anchored-relative` | N03–N04 |
| OT03 | `cor:relative-cap` | N05 |
| OT04 | `prop:joint-owner-caps` | N05 |
| OT05 | `prop:anchored-typed-source` | N06 |
| OT06 | `thm:relative-transfer` | N07 |
| OT07 | `thm:relative-real-closure` | N08–N09 |
| OT08 | `lem:relative-finite-avoidance` | N10 |
| OT09 | `cor:relative-closed-sap` | N10 |
| OT10 | `lem:full-owner-transversal` / `thm:joint-transversal` | N12–N14 |
| OT11 | `lem:packet-collision` | N11 |
| OT12 | `lem:packet-origins` | N14 |

The first six are in `sections/anchored_relative_completion.tex`, the next
four in `sections/owner_transversal_direct.tex`, and the final two in
`sections/hkn_packet_reservoir.tex`. The two labels on OT10 name ONE result.
The examples, language-action definition and scope remarks are included as
explanations of these contracts, not counted as further theorem exports.

Use an inhabited, countable, transitive original real source M in a finite
complete binary language. Every distinct pair has exactly one named raw
diversity atom; equality is the separate atom Id. Original raw orbitals are
symmetric, and M is homogeneous for finite induced maps. Its actual age
has AP, semantic homomorphic CCO, and the prepared triangle-fullness law:
every finite complete diversity diagram whose triangles are actual legal
triangles embeds in M. Binary legality includes the actual pair palette,
so structures of size at most two are covered as well. All represented
products are existential relational compositions on M. They are not
formal products in a freely presented colour algebra.

Retain the hypotheses of the existing RAW provider, including countability
where its joint lifting and exact quotient-source theorems use countable
back-and-forth. Some arguments below use less: the finite closed-walk
calculation, finite-group transport, and abstract finite-action avoidance
do not require countability. This does not remove countability from the
actual-source export signatures that invoke that provider.

Import the following prepared results rather than prove them again.

* `raw_exact`: represented product laws and same-sort commutation;
  actual quotient/mixed orbital pullbacks; nested mixed-orbit recognition;
  finite joint real/exact-sort lifting; exact quotient-source homogeneity;
  original complete-diagram triangle fullness and semantic CCO.
* `real_closure` C11: singleton closure acl(a)=F[a], and, with one minimal
  infinite invariant direction, acl(A)=F[A] for every finite real A.
  Its supporting minimal-infinite exactness and full-lattice facts remain
  available. This is not a harmless-owner assertion.
* `acl_owner_geometry`: the global cut R_E and its intersection calculation;
  harmlessness of finitely many owners whose kernels contain every minimal
  infinite invariant equivalence; orbit/acl conversions; simultaneous
  finite-action avoidance with the internally proved finite-coset-cover
  lemma. Its full invariant lattice is essential, not an exact-only lattice.
* `finite_packets` C26–C28: the finite thin group, regular packet action,
  subgroup interval and endpoint transport laws. In particular F is the
  greatest finite-class invariant equivalence, and a full packet has |G|
  points. Do not redevelop these results or assume translations act freely
  on the external colour palette.

For N03–N07 fix an invariant equivalence E>Id which is REACHABLE: there
is a nonempty positive word of raw atoms whose represented product is E.
N02 states its weaker, independently quantified relation calculation.
Write Q=M/E, pi for the actual quotient map, and bar(a)=E;a;E. A quotient
pair has one actual orbital, whose full raw pullback is one such saturated
relation; this pullback can contain several fine atoms. The partial finite
diagram P uses distinct formal vertices, specified irreflexive diversity
edges, and at most one specified colour per unordered pair. A map lambda
to Q is compatible if every specified a-edge has its owner pair in the
quotient orbital supported by bar(a). Lambda need not be injective.

For N08 onward impose the RESIDUAL source hypotheses: finite-exact
normalization, a minimal infinite exact equivalence E, and R_E=F=Sigma(Id).
Normalization means there is no nonidentity finite-class FULL RAW exact
invariant equivalence. The thin bottom is the actual finite elementary
abelian group G, with t_g its named thin translation. Put H=E intersect F,
identified with the subgroup of G preserving an E-owner. Fix B a FINITE,
NONEMPTY, G-INVARIANT actual induced substructure of M/E. Define
N_B=pi^{-1}(B), with each individual owner predicate P_b named, and
Gamma=Aut(B) in its full actual quotient orbital language. F[A] means the
union of packets meeting A, including F[empty]=empty. This B condition is
specific to the residual branch; the generic finite-owner branch permits
empty B and does not require G-invariance.

There is no safe strong-closed S assumption, NR2, selector, root frame,
HKN reservoir, EPPA theorem, or owner-section hypothesis in this local
package. Conditional EPPA in N07 is a reduction with explicit premises.

## N02: Closed owner walks and saturation — OT01

Quantify over every invariant equivalence E, every finite nonempty list
w_1,...,w_m of factors, each either E or an actual raw atom, with at least
one E-factor, and every list of actual owners X_0,...,X_m with X_m=X_0.
Require equal successive owners at an E-factor and existence of an
a-edge between the successive owners at an a-factor. Then
Id is contained in W=w_1;...;w_m. If E has a chosen positive atomic word
presentation, the cyclic word obtained by expanding the E-factors has a
colour-preserving homomorphism to M. No injectivity is asserted, and
reachability is needed only for this last expansion, not for Id<=W.

For an atomic factor set C_i=E;a;E; for an E-factor set C_i=E. The
owner hypothesis gives X_{i-1} times X_i contained in C_i, not merely
one pair in C_i. Indeed an existing a-edge supplies witnesses for every
choice of endpoint representatives. Choose u_i in X_i, setting u_m=u_0.
Then (u_0,u_0) belongs to the product of the C_i. By associativity,
commutation of ORIGINAL invariant relations, and E;E=E, that product is
E;W;E. Since W already contains an E-factor, E;W;E=W. Thus one actual
diagonal pair belongs to W. Invariance and original point transitivity
carry this to every diagonal pair, proving the claimed inclusion.

Membership in a finite represented product supplies its intermediate
points by successive existential elimination. For each E-factor replace
its witness segment by witnesses for the fixed positive word representing
E. The resulting finite list is a walk with its last point equal to its
first, hence a homomorphism of the displayed cyclic word. Intermediate
points, including nonadjacent points, may coincide. No independently
chosen representative tuple is claimed to realize the original fine
atomic edges. This distinction is exactly why saturation is used first.

An actual simple specified cycle only uses diversity edges, but its
homomorphic realization need not be a simple cycle. Symmetry permits
traversing a private word path backwards: its reverse represented product
is again E. Same-sort invariant commutation is valid here; it must not be
transported without proof to unrelated mixed original sorts.

## N03: Private-path augmentation and anchored completion — OT02

For every finite P having a raw homomorphism, every compatible lambda,
every complete induced A contained in P, and every induced embedding
j:A->M satisfying pi j=lambda on A, there is a homomorphism f:P->M
extending j and satisfying pi f=lambda everywhere. Completeness of A
means all its distinct pairs already have their actual diversity colours.
Taking A empty gives the basic assertion. Neither statement assumes SAP
or infinite E-classes.

Start with any raw homomorphism h of P. Since A is complete, h restricted
to A is injective and induced: preservation of the unique fine atom on
each pair gives reflection in this complete language. The map h(a)->j(a)
is therefore a finite induced isomorphism. Extend it by homogeneity and
postcompose h to obtain f_0 agreeing with j on A.

Let B_0=lambda(V(P)). For each owner choose one representative, using an
already anchored point in that owner whenever possible. Take the actual
finite induced structure T on these representatives together with j(A).
View T as a fresh labelled copy identified with P precisely on A. A
representative already equal to some j(a) is represented by that same
anchor vertex, not a second vertex. The other vertices of T are formal
vertices distinct from P\A even if their actual locations equal some
f_0(x); homomorphisms are allowed such collisions.

Delete equality factors from a positive presentation of E. Its remaining
list is nonempty, since E>Id, and consists of diversity atoms. In fact its
length is at least TWO: a single diversity atom is irreflexive whereas E
is reflexive. Its product is still E. For every x in P\A add a path from x to the chosen T-vertex
in owner lambda(x), using this word. Use new interior vertices private
to this path. Endpoints are formally distinct, and at least one fresh interior vertex
occurs on every private path, even when its owner representative is an
old anchor vertex. The partial graph remains finite, and no old unordered
pair receives conflicting colours.

Every simple specified cycle in the augmented graph is realizable. If it
uses no private path, it lies in P union_A T. Map P by f_0 and T by their
actual locations. These assignments agree on A, so define a single
homomorphism of that union. There are no specified P\A-to-T\A edges
to check. If a cycle uses a private path, each interior degree-two vertex
forces traversal of that whole path. Contract each traversed path to one
E-factor, reversing its word if the traversal orientation requires it.
All remaining edges retain their old raw atoms. Label old P vertices by
lambda and T vertices by their actual owners. This is a closed owner
walk of N02, with at least one E-factor. Expanding the witnessed product
gives a homomorphism of the entire specified cycle.

Raw semantic CCO now gives one homomorphism k of the whole augmentation.
Its restriction to the complete T is an induced embedding. Homogeneity
extends the inverse map from k(T) to the prescribed actual T; postcompose
k with that ambient automorphism. T is now fixed pointwise. Every private
path has word product E, so its initial point lies in the same E-class
as its fixed terminal representative. The restriction to P is the required
f. In particular, the final alignment fixes the real anchor j, not merely
its owner labels. Do not require the initial f_0 to have the desired owner
assignment; only its restriction to A is constrained at that stage.

## N04: SAP injectivization and the protected base — OT02 continued

Under the ADDITIONAL assumptions that Age(M) has SAP and every E-class
is infinite, the f in N03 can be chosen injective. This stronger statement
is a separate branch; raw SAP is not an assumption of the basic theorem
or of the residual global theorem.

First prove the finite-base orbit fact. For finite real C and v outside C,
strongly amalgamate arbitrarily many copies of C union {v} over the SAME
complete C. The resulting finite age member embeds in M. Align its base
with C by homogeneity. Each copy of v has the same induced type over C,
so homogeneity places it in the orbit Aut(M/C)v. The copies are distinct;
the orbit is infinite. This establishes the fact for all finite C.

For any finite list of named infinite E-owners, choose a representative
of each outside C union {v}. Apply the preceding fact to the enlarged
finite real base. Its stabilizer fixes C and the owner names, and v is
outside that enlarged base. Its orbit is infinite and contained in the
orbit over C and the named owners. Thus the latter orbit is infinite.

If f identifies two formal vertices, at least one member x of this
collision is outside A, since f restricted to A is an embedding. Let C
be the set of images of specified neighbours of x. All incident colours
are irreflexive, so f(x) is outside C. The orbit of f(x) over C and ALL
owners lambda(V(P)) is infinite. Choose an orbit member outside the finite
current image f(V(P)). Replace ONLY f(x) by this point. The witnessing
automorphism fixes C and each named owner, so every displayed incident
colour and lambda(x) are retained. All other vertex images, including
every anchor, stay unchanged.

The number of unordered equal-image pairs strictly decreases: x is now
distinct from every other image, and other equalities do not change.
This natural-number measure terminates the procedure. The completed map
is injective and satisfies the same constraints. It is an embedding into
the induced complete structure pulled back onto V(P); an incomplete P
does not have absence of unrecorded colours reflected.

Do not include all anchored images in the fixed set C. A collision may
be with an anchored vertex having no specified edge to x, in which case
fixing that image would make the required move impossible. Protecting A
means changing no image of an A-vertex, not requiring each local moving
automorphism to fix all of A. This distinction also governs N11–N12.

## N05: Individual spectra, equality and joint caps — OT03–OT04

For OT03 quantify over an initially unspecified unordered pair {x,y}
in a finite raw-completable P and a compatible lambda. Let D_xy be the
set of equality-inclusive actual atoms col(h(x),h(y)) over ALL raw
homomorphisms h:P->M. Let C_xy be the set of raw atoms in the full
pullback of the actual quotient pair orbital of (lambda(x),lambda(y)).
The corresponding set obtained from homomorphisms with pi h=lambda is
exactly D_xy intersect C_xy. Also there exists ONE homomorphism satisfying
the owner caps on ALL pairs simultaneously. This last existence statement
does not assert that arbitrary separate choices from the intersections
can be realized together.

Necessity follows by applying pi to a realizing pair. For a diversity
atom a in the intersection, add xy=a to P. Its membership in D_xy
provides a raw witness of the augmented diagram; its membership in C_xy
makes the new edge compatible. N03 applies. The common-caps statement
is simply N03 applied to P before any extra edge prescriptions.

Equality needs a distinct argument because P has diversity edges only.
If Id lies in D_xy, choose a witness h with h(x)=h(y). Identify x and y
as formal vertices. No diversity edge collapses to a loop, and any two
specified edges which become the same pair have equal colours, since
h preserves both. Thus the identified relational diagram is a valid
raw partial diagram and is raw-completable. If also Id lies in C_xy,
then lambda(x)=lambda(y): the pullback of quotient equality is E, and
an actual diagonal can lie in no other quotient orbital. Lambda therefore
descends to the identified diagram. Apply N03 there and pull the map
back along identification. This realizes equality with the prescribed
owners. The argument extends to any imposed finite equality partition
provided lambda descends and the identified raw diagram is completable;
it does not treat equality as a diversity edge.

Under the N04 hypotheses the analogous D_xy for injective raw completions
uses diversity atoms only. Add one such atom and invoke N04. Equality
apart, there is no gap between the two versions of D_xy: every diversity
atom in the original homomorphic spectrum gives a raw-completable
augmented diagram. Assign it the owners of a witnessing homomorphism
and apply N04 to obtain an injective raw realization. For an atom also
in C_xy, use the originally prescribed lambda instead. Thus its diversity
part is already the injective spectrum whenever the N04 hypotheses hold.
Equality
cannot occur between distinct vertices of an injective completion. If
using a protected anchor together with identifications, the identified
anchor must still be an embedding; an equality identifying two distinct
anchored vertices is forbidden by this condition.

For OT04 fix ANY set S of previously unspecified unordered pairs and
prescribe one diversity atom a_xy for each. Since P is finite, S is
finite. Let P_S retain every old edge and all these new edges. Retain
an arbitrary complete anchor A with compatible j, or take it empty.
There exists a homomorphism P_S->M extending j with pi f=lambda iff
(i) every new atom is owner-compatible and (ii) EVERY specified simple
cycle of the WHOLE P_S admits a raw homomorphism. No raw completion of
P is a further premise: (ii) and semantic CCO give a completion of P_S.
The old-edge compatibility of lambda is a standing premise.

Necessity restricts one realization to its edges and cycles. Conversely,
CCO gives a raw homomorphism of P_S; (i) plus old compatibility make
lambda compatible on all its edges, and N03 supplies the required
owner-constrained anchored realization. N04 gives the injective version
under its additional assumptions. The cycle quantifier includes mixed
old/new cycles and cycles with chords; it is not a collection of separate
edge tests or triangle tests. The source four-cycle example shows why:
three same-column edges along a path force its endpoints to agree in
column, contradicting a different-column closing edge, despite all four
individual owner caps being admissible. This is raw CCO obstruction,
not a further owner-specific obstruction.

## N06: The actual named typed source and full Gamma extensions — OT05

Let B be ANY finite actual induced substructure of Q, possibly empty,
and N_B its induced real preimage with one named predicate per owner.
Then N_B is homogeneous. Its finite complete typed age consists exactly
of triangle-legal raw complete diversity diagrams, with owner labels in
B compatible with every edge. Its age has AP and typed semantic
homomorphic CCO. Under raw SAP and infinite E-fibres its age has SAP.
Here a typed edge palette is the actual fine-colour support of the
corresponding owner pair; owner equality does not identify real vertices.

The additional extension contract quantifies over every gamma in Aut(B)
and every finite RAW partial induced isomorphism p of M with domain and
range in N_B satisfying pi p=gamma pi on its domain. There exists ONE
ambient sigma in Aut(M) extending p and carrying EACH b in B to gamma(b),
including owners not represented in the domain of p. No coherence in
(p,gamma) and no homomorphism Gamma->Aut(M) is claimed.

Choose a finite complete actual C contained in N_B that contains dom(p)
and one representative of every owner b in B. The assignment
lambda=gamma pi on C is compatible: gamma preserves each actual quotient
pair orbital and fixes raw fine-colour names in the language action.
The complete domain dom(p), embedded by p, is a compatible anchor.
N03 gives a homomorphism of C with precisely this lambda extending p.
Since C is complete this map is injective and induced without SAP.
Homogeneity of M extends it to sigma. Each chosen representative forces
sigma(b)=gamma(b), so sigma preserves the entire union N_B. For B empty,
C and p are empty; the same assertion is vacuous and an ambient identity
works. Taking gamma=identity proves named-owner homogeneity.

A finite triangle-legal complete typed diagram first embeds raw into M
by triangle fullness, then N03 re-embeds it with its specified owners.
This proves the age description. Conversely any actual finite member
has legal triangles and compatible owner labels. AP follows explicitly:
realize both finite extensions of a common finite base in N_B, align
their base maps by named-owner homogeneity, and take the finite induced
union. Identifications away from the base are allowed for AP.

For typed CCO, a partial diagram has allowed owner-compatible colours
and every specified cycle has a typed realization. Forget labels to
obtain raw cycle realizations; raw CCO and N03 restore all labels in
one map. Under raw SAP and infinite fibres, first use raw SAP to realize
the union of two factors with distinct off-base formal points. Their
owner labels agree on the common base, so N04 gives an injective typed
realization. Its induced finite image is a strong amalgam. No SAP is
asserted by the basic typed-source contract.

Gamma acts on this AGE by P_b -> P_gamma(b), fixing every fine atom.
The cap description proves closure under this finite language action.
Equivalently the ambient extension just proved realizes each relabelled
finite diagram. The choices of ambient lifts are independent witnesses.

## N07: Conditional ordinary-EPPA transfer — OT06

Assume ordinary EPPA for Age(Q). Assume also, FOR EVERY finite actual
induced B contained in Q, Gamma_B-EPPA for Age(N_B), where Gamma_B=Aut(B)
permutes only owner predicates and fixes EACH original fine atom.
Then Age(M) has ordinary EPPA. Reachability and all actual-source
hypotheses supporting N06 remain in scope. This theorem does not prove
the typed-language EPPA premise or assume coherent EPPA.

Given finite A in M, take a single quotient EPPA witness for pi(A).
Embed that finite witness into the actual Q over pi(A): realize it in
Q and align its included pi(A) by quotient homogeneity. Denote the
resulting finite actual induced structure by B. For every partial
automorphism p of A define its induced map on projected domain owners.
It is well-defined and injective because p preserves E, a union of raw
atoms: two domain points have equal owners exactly when their p-images
do. It preserves the actual quotient orbital of every owner pair,
since the raw atom of any representative pair is preserved. Thus it
is a partial quotient automorphism of pi(A).

Choose gamma_p in Aut(B) extending this projected map, using the ONE
quotient EPPA witness. Regard A with its actual owner labels as a typed
member over B. Each (p,gamma_p) is a valid partial language-action
automorphism. Take ONE finite typed EPPA witness W for all such pairs.
Forget owner predicates. W remains a finite raw age member, and each
extending permutation preserves every raw atom, hence is a raw
automorphism extending p. This proves ordinary EPPA for A.

Keep the quantifier order: first one B for the finite quotient input,
then choices of gamma_p, then one W extending all requests. Independent
witnesses for different p would not suffice. Empty-real-domain requests
can carry a prescribed gamma; the language component is still part of
the request. Nothing requires gamma_p gamma_q=gamma_pq.

## N08: Residual unary closure without joint lifting — OT07

Return now to the residual hypotheses of N01. For EVERY finite real
A contained in N_B, including empty A,

    acl_(N_B)(A) = acl_M^eq(A union B) intersect N_B = F[A].

Moreover F[A] is definable over A in N_B by the finite literal named
thin translations. These equalities are established BEFORE proving
homogeneity of N_B and do not depend on joint lifting.

First E is the unique minimal infinite invariant equivalence. Any
different minimal infinite invariant E' is exact by the prepared
minimal-infinite exactness theorem. E intersect E' is an exact invariant
equivalence; minimality implies it has finite classes, and normalization
then forces it to be Id. For each atom a contained in E', its square
is contained in E', so E intersect a squared=Id (the diagonal inclusion
uses symmetry and seriality). Hence E' is contained in the GLOBAL cut
R_E=F, contradicting its infinite classes. This also explains why the
global meaning of R_E and full RAW exact normalization cannot be dropped.

Apply the existing one-direction real_closure C11 to obtain
acl_M(A)=F[A] for every finite real A. Since the sole minimal infinite
equivalence E is contained in the kernel E of every owner we name,
the harmless-owner theorem gives
acl_M^eq(A union B) intersect M=acl_M(A). Owners are fixed individually
as actual imaginary elements, not merely setwise as a finite subset.

For x in N_B outside F[A], the latter equality says its orbit under
Aut(M/A,B) is infinite. Every such ambient automorphism preserves N_B,
all raw atoms and each named owner predicate. Its restriction belongs
to Aut(N_B/A). The latter orbit contains the former infinite orbit;
therefore x is not algebraic in N_B over A. This implication needs
only an inclusion of acting groups after restriction, not surjectivity.
If x belongs to F[A], regularity gives x=t_g(a) for some a in A and
g in G. The graph of t_g is a named thin atom, so this is a unique
definable value over a. G-invariance of B keeps this value in N_B.
Thus F[A] is contained even in definable closure in N_B and equals
both closures displayed above.

For empty A, F[A] is empty and the original source is infinite and
transitive, so real acl(empty) is empty; harmlessness still applies
to the finite imaginary owner set. This is not an exception requiring
a real anchor. Finite union of the formulas defining the finitely many
t_g(a) gives a formula for F[A]; for A empty use the false formula.

## N09: Named N_B homogeneity and actual language actions

The source OT07 also states named-owner homogeneity separately. Give
its independent lifting proof rather than using it circularly in N08.
Let p be a finite induced raw-colour partial isomorphism in N_B
preserving every owner predicate. Extend the request by fixing ALL
the finite actual E-owner classes B in the joint real/E-sort language.
Real/real pairs are preserved by p; owner/owner pairs are fixed.
It remains to check EVERY mixed real/owner orbital, including owners
not occurring among the real domain labels.

For an original atom a, its real-to-E-owner pullback is Id;a;E=a;E.
Commutation and idempotence give a;E=E;a;E. Consequently the mixed
orbital depends only on the actual quotient pair orbital of
(pi(x),b), not on x's representative within its owner. Since p preserves
pi(x) and b is fixed, this pair orbital is unchanged. The finite joint
request is therefore a genuine induced partial isomorphism. Prepared
joint exact lifting supplies one ambient automorphism fixing all of B
and extending p. Its restriction to N_B proves homogeneity.

The same calculation handles a prescribed gamma in Aut(B): if p sends
each occurring owner b to gamma(b), extend its owner component by gamma
on all B. Owner/owner and mixed pair orbitals remain preserved. Joint
lifting yields an ambient lift inducing gamma, preserving literal raw
atoms, and commuting with every t_g by their definability. Its restriction
preserves the union N_B and sends P_b to P_gamma(b). This is consistent
with the independently proved N06 extension assertion. In either proof,
retain the countable-source hypothesis of the imported lifting API.

Do not infer that a map preserving only REAL colours automatically
extends by arbitrary owner data; mixed-orbit verification is necessary.
Do not infer a group section from existence of these separate lifts.
Gamma's action on the LANGUAGE has identity effect on all raw colour
names and all named t_g symbols, although its point realizations need
not preserve individual owner predicates.

## N10: Relative simultaneous avoidance and closed SAP — OT08–OT09

OT08 quantifies over finite induced C contained in A contained in N_B,
with F[C]=C and F[A]=A, and every finite Z contained in N_B\C.
There is g in Aut(N_B/C), preserving each named owner, such that
g(A\C) intersect Z is empty. This moves the ENTIRE finite off-base
set simultaneously. It is not obtained by separately choosing new
images for its individual points.

By N08, acl_(N_B)(C)=C. Hence every a in A\C has infinite orbit under
K=Aut(N_B/C). Apply the existing abstract finite-action-avoidance theorem
to K acting on N_B, moving set A\C, and forbidden set Z. It gives one
g avoiding all point-target coincidences. The finite-action theorem,
including its finite-coset-cover proof, is already prepared and has no
countability assumption. Its actual application here imports the
source-dependent closure equality, not an extra abstract group axiom.
If the moving or forbidden set is empty the identity suffices.

For OT09 take any two finite full-F-closed typed induced structures
and embeddings of a common finite full-F-closed base. Realize them in
N_B and use N09 homogeneity to arrange that the two base embeddings
agree pointwise. Their images may overlap off the base. Apply OT08
to the second image, with base equal to the common image and Z the
off-base points of the first image. It fixes the base and makes the
off-base sets disjoint. The induced union is a strong amalgam in the
actual named-owner age.

Its F-closure is finite and stays inside N_B. Indeed it is already
F-closed when both factors are full packets, since F of a union is
the union of their F-closures. Taking closure explicitly is harmless
and gives the source's stated output. Closure adds points and relations,
not identifications. The intersection of the original factor images
is exactly the base. Empty base is allowed, since acl_(N_B)(empty)
is empty, and gives JEP for finite full-packet structures. No claim
of raw SAP for arbitrary finite, nonclosed bases follows.

## N11: Separation of collisions in recorded packet diagrams — OT11

Quantify over finite P partitioned into literal disjoint regular full
G-packets, with total named functions t_g and exactly one actual B-owner
label per point. The compatibility own(t_g o)=g own(o) follows from the
owner- and function-preserving map q required below; it is not a further
independent realization assumption.
Interpacket records are either absent or one COMPLETE fine matrix
of colours outside F. Suppose q:P->N_B preserves owners, all packet
functions and records, and is injective on each packet. Let A_* be
a union of whole packets which is a complete induced substructure of
P, and suppose q restricted to A_* is an induced embedding. Then
there exists a globally injective record-preserving q' with all packets
in distinct actual F-classes and q'=q on A_*. Its induced pullback
is a completion on P's original vertex set. The base can be empty.

Every packetwise injective function-preserving map sends a full packet
ONTO one actual F-class: its image contains t_g q(o) for every g,
which exhaust that class. Thus two source packets have either equal
or disjoint image packets. Recorded neighbours cannot have equal
image packets because their preserved cross-colours lie outside F.

If two distinct packets collide, choose a colliding packet Pi outside
A_*. This is possible since q is injective on the protected full-packet
base. Let S be the union of the ENTIRE image packets of recorded
neighbours of Pi. Put C=F[S]=S. The packet Q_0=q(Pi) is disjoint from
C: otherwise it equals one recorded neighbour's image packet, contrary
to a recorded nonthin edge. Thus C union Q_0 is a finite closed
extension of C. Let Z be the union of all other currently used packet
images outside C, optionally also including Q_0. It is a finite subset
of N_B\C, even when a different unrecorded packet has image Q_0.

Apply OT08 to C contained in C union Q_0 and forbidden Z. Obtain an
owner-preserving automorphism alpha fixing C and moving Q_0 away from
Z. Since it fixes C pointwise and Q_0 was disjoint from C, alpha(Q_0)
is also disjoint from C. Replace only q on Pi by alpha composed with
q. All its internal equations survive because alpha commutes with t_g;
all recorded edges survive because their other endpoints lie in fixed
C. All other recorded pairs are unchanged. The individual protected
vertex images never change, even if alpha itself moves some of them.

The new image of Pi avoids every other used packet: those in C by
disjointness, and all others by Z. Hence the number of unordered
colliding packet pairs strictly decreases, and none is introduced.
Finite descent yields q'. No unrecorded collision target was included
in the fixed base merely because it was a current image. Completion
preserves displayed records and adds unspecified colours; it does not
reflect the absence of a record, as an HKN embedding would require.

## N12: Origin-transversal age, triangle fullness, CCO and SAP — OT10

Define K=mathcal U_B as the finite owner-typed complete diagrams which
have an actual realization in N_B taking distinct vertices into
DISTINCT full F-packets. Its allowed pair palette for owners s,t is
P_st=L_st\F, where L_st is the actual raw support of that owner pair.
For s=t this is the nonthin part of E: subtracting F or H gives the
same support inside E. Repeated owner names are allowed; equality
and thin atoms are excluded between distinct formal vertices.

First establish the protected semantic completion assertion. For every
finite partial typed diagram with edges in these palettes, assume every
specified simple cycle has a typed homomorphism to N_B. Given any
complete protected subdiagram already packet-separated and embedded in
N_B, there is one homomorphism of the whole diagram extending it,
preserving owners and records, and separating ALL formal vertices into
distinct F-packets. Forget labels, use raw CCO, and apply N03 with the
given anchor. This gives the initial homomorphism with correct owners.

If two formal vertices occupy one packet, choose a colliding off-base
vertex x. Let C be the finite set of current images of its specified
neighbours. Since every incident colour lies outside F, f(x) is outside
F[C]. N08 says the owner-preserving Aut(N_B/C)-orbit of f(x) is infinite.
Each F-packet is finite, so this orbit meets infinitely many packets.
Choose an orbit point outside all currently used packets and change
ONLY the image of x. Incident records and its owner survive; the
protected images are unchanged. The number of unordered same-packet
pairs strictly decreases. This proves the completion assertion by finite
descent, with no raw SAP assumption. In particular typed semantic CCO
has a packet-separated, hence injective, output here.

For triangle-definedness, a finite complete typed diagram with allowed
P_st colours and legal raw triangles embeds raw by original triangle
fullness. N03 realizes its owner assignment. Completeness makes this
map injective, and nonthin colours already force distinct packets.
One may also use the preceding separation argument. Conversely an
actual realization has all these legal triangles. Thus the condition
is precisely actual raw triangle legality together with the typed
pair palettes; it does not impose a newly invented coloured triangle
table on owners. Boundary sizes zero, one and two use the allowed
palettes and nonempty actual owner classes.

For SAP, realize the two finite K factors and inflate each selected
origin to its full G-packet. A common transversal base has a uniquely
determined full-packet isomorphism t_g a -> t_g a' extending its
given base map. The transport law shows this is an induced named-owner
map. Align these bases by N09, then use OT09 to strongly amalgamate
the full-packet factors. Select one origin in each resulting packet,
retaining the original factor origins. This selection is possible:
their only common packets are the inflated common base, where their
origins agree. The resulting K structure is the desired strong amalgam.
Taking the base empty gives JEP. Heredity holds by restriction.

Each named sort has arbitrarily many vertices: a fixed owner class
is infinite and every packet finite. Equivalently apply the already
proved SAP repeatedly to a one-point diagram in that sort. These
facts support both the countable construction in N14 and primitivity.

## N13: Primitivity through a GLOBAL original equivalence — OT10

Let U be the homogeneous limit constructed in N14, whose age is K.
Fix owner s and suppose an Aut(U)-invariant equivalence on its named
sort is neither equality nor universal. Since finite same-sort pair
maps extend by homogeneity, its diversity support is a nonempty proper
union D of LITERAL fine atoms in P_ss. Thus it suffices to exclude
such D closed under composition on distinct transversal vertices.
For a,b in D, SAP over the middle singleton realizes an a,b path on
three distinct packets. Its outer colour c exists and lies in D by
equivalence transitivity. More generally every actual nonthin output
atom of a;b is in D: its triangle realizes in K by triangle-definedness.

For g in H, suppose D intersect gD is nonempty. Choose a with both
a and ga in D; involutivity permits this orientation. Given b in D,
choose a realized three-packet triangle of colours (a,b,c), so c in D.
Translate its first point by t_g. Owner labels remain s, and distinct
packets stay distinct. Its colours become (ga,b,gc), hence gc in D.
Translate instead the third point of the original triangle. Its
colours become (a,gb,gc), so gb in D by transitivity of the equivalence.
All these are valid K triangles; changing a point within its packet
does not collide with the other two. Thus gD contained in D, and
g squared=0 gives gD=D. Put H_D={g in H:gD=D}; this is a subgroup.

Define on the WHOLE original M the raw invariant relation

    J = Id union {thin t_g : g in H_D} union D.

It is reflexive and symmetric, lies in E, and is invariant under the
ORIGINAL Aut(M), since it is a uniform union of original globally
named atoms. Prove composition closure inside owner s. Thin/thin
products follow H_D being a subgroup; thin/D products follow gD=D.
For D/D products, nonthin outputs lie in D as above. If a,b in D
produce thin t_g, the witnessed triangle and transport imply b=ga
(up to the harmless interchange of a,b, since all are symmetric).
Thus D intersect gD is nonempty, so g belongs to H_D. Equality output
is included already. This exhausts all original output atoms.

Every composable pair of J-edges lies within one actual E-owner class.
Original transitivity moves one point of that class into owner s and
therefore carries the entire class there, preserving every old atom.
The preceding composition check applies and transports back. J is
therefore a GLOBAL original invariant equivalence, not a local new
relation defined by a chosen owner section.

J has infinite classes. Choose an actual realized D-edge xy in owner
s. For every positive integer n, strongly amalgamate n copies of
this COMPLETE two-point K structure over the same singleton x.
This gives n distinct D-neighbours in distinct packets. By the very
definition of K, this finite structure realizes in N_B, hence M.
Its n+1 points lie in one J-class. Original transitivity makes all
J-classes equipotent, so their sizes cannot be finite. This reasoning
does not require embedding the entire infinite U with a fixed origin
choice into M.

The full invariant-equivalence lattice is finite. Every infinite-class
invariant equivalence contains a minimal infinite one. By N08 the only
such minimum is E, so E contained in J. Since J contained in E,
equality follows. Comparing nonthin supports gives D=E\F=P_ss,
contradicting properness. Every individual named owner sort is
primitive. This uses the FULL lattice and the original global colour
union; primitivity of a local sort alone would not provide either.

## N14: Countable limit, inflation, origins and recovery — OT10–OT12

Here is a concrete countable route, so invoking a separate unformalized
Fraisse theorem is unnecessary. K has countably many finite labelled
structures and finite embeddings because its relational signature and
owner set are finite. Enumerate representatives of every finite
embedding A->D in K. Build a chain of finite K members, using SAP
(AP would suffice for existence) and JEP, which eventually realizes
every extension request consisting of such an embedding and an
embedding of A into the current chain. Include empty A requests.
An explicit fair schedule at stage n considers the first n listed
finite extension types and all embeddings of their bases into the
first n earlier stages. There are finitely many such requests; carry
them out successively by AP, retaining the current stage by inclusion
after relabelling the amalgam. Every fixed request eventually occurs.

The union U is countable, every finite substructure lies in K, and
empty-base requests embed every K member into U. For any embedding
A->U and extension A->D in K, the finite image of A lies in one
stage and its request is eventually met. Thus U has the finite
extension property. Alternating this property along enumerations of
domain and codomain extends every finite induced isomorphism between
two such countable structures to an isomorphism: add the next missing
domain point using its finite induced extension, then apply the same
argument to the inverse for the next missing codomain point. All
stages are finite, their maps extend, and their union is bijective
and preserves every relation. Applying this to U with itself proves
homogeneity. Repeated one-point SAP requests, or the unbounded finite
sort sizes in N12, ensure every owner sort is infinite. This U is U_B.

Define the inflation I(U) on U times G. Within one packet put
col((x,g),(x,h))=t_(g+h), including equality when g=h. Put
own(x,g)=g own(x), t_k(x,g)=(x,k+g), and for x different from y put

    col((x,g),(y,h)) = (g+h) col_U(x,y).

These are actual atoms by the imported transport law. Every finite
full-packet substructure of I(U) embeds into N_B: restrict to its
coordinate-zero origins, realize their finite K diagram in N_B,
and send (x,g) to t_g of its realized origin. Regularity proves
injectivity, owner equivariance gives the labels, and transport
gives every interpacket colour. Conversely every finite full-packet
structure of N_B is the inflation of the K structure on ANY chosen
one origin per packet. This is an existence of finite choices,
not a canonical or equivariant section.

To prove recovery rigorously, verify a CLOSED extension property for
I(U). Let A contained in D be finite full-packet actual structures
in N_B, and let f:A->I(U) be an induced named-owner embedding.
Every such map commutes with t_g because thin graphs define them,
so it maps each whole packet onto one coordinate packet of I(U).
For each packet of A choose its origin o_i to be the UNIQUE preimage
under f of that image packet's coordinate-zero point (x_i,0).
This adapted choice is crucial: now the origin map o_i->x_i is
literally an owner-preserving fine-colour embedding into U. Choose
arbitrary origins on the remaining packets of D. Their full finite
transversal belongs to K. U's extension property extends the existing
origin map to that transversal; inflate by the equations above.
The resulting embedding D->I(U) extends the GIVEN f on every point
of A. No global origin section or coherent gauge choice is needed.

N_B has the same closed extension property: realize a finite D in
N_B and use N09 homogeneity to align its embedded A with the supplied
image. Both N_B and I(U) are countable, and every finite subset has
finite F-closure. Enumerate their points. Starting with the empty
map, alternately add the next point together with its whole packet,
using the closed extension property on either side. The union is
a bijective owner-preserving raw isomorphism commuting with all t_g.
Thus full packet inflation of U recovers N_B. This construction proves
the asserted recovery without first declaring inflated generic
homogeneity as an opaque axiom. Homogeneity of I(U) also follows from
the isomorphism and N09. Countability is used explicitly here.

Finally OT12 applies to EVERY finite recorded packet diagram of N11
equipped with origins o_i and beta_i=own(o_i), whose recorded pair
matrix is exactly

    col(t_g o_i,t_h o_j) = (g+h)c_ij,  c_ij outside F.

Form its partial origin diagram with vertex i of sort beta_i and
edge c_ij exactly for recorded pairs. Any packet-separated typed
completion of these origins in N_B lifts by
hat(e)(t_g o_i)=t_g e(i). Uniqueness of the regular packet coordinates
makes this well-defined. Distinct target packets and regularity make
it globally injective; owner labels and every recorded fine matrix
are preserved by transport. An injective completion in the abstract
U_B gives the same conclusion by inflating and using the established
isomorphism I(U_B) to N_B. The missing records impose no conditions.

If a complete embedded full-packet source base is prescribed, its
image under hat(e) is a complete induced named-owner copy. The map
from that image to the prescribed copy, determined by the original
source vertex correspondence, is an induced isomorphism. N09 extends
it to an automorphism of N_B; postcomposition aligns the whole base
pointwise. The word "unique" refers to this determined finite map,
not uniqueness of its ambient extension. All t_g equations survive.
This completes the origin reduction with the protected-base clause.

Gamma permutes only owner tags on K and fixes each fine colour name:
ambient finite-owner lifts in N09 realize the relabelled finite
diagrams and commute with t_g. In particular gamma(gb)=g gamma(b)
on the G-invariant B. This provides the compatible literal language
action on origins and full packets. It does not provide a preferred
isomorphism I(U_B)->N_B, a canonical origin in each packet, or a
group-theoretic section of ambient owner lifts. None is needed for
any of the twelve exports.
