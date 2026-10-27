# RAW exact geometry: additional proof details

These notes expand the existing human proofs for formalization. The source
map, hypotheses, claim DAG and current implementation tasks are in
`module.json`; the generated [module index](README.md) lists their IDs.
All statements here concern actual represented relations. They supply no
abstract colour-table representation theorem.

## N01: Source, orbitals and seriality

Use a finite set of named sorts with nonempty carriers, a countable total
real universe, and a finite complete binary relational language. Homogeneity
means that every finite sort-preserving induced partial isomorphism extends
to an automorphism. The automorphism group is transitive on each original
sort. Same-sort diversity atoms are symmetric and irreflexive; logical
identity is a separate atom. Cross-sort atoms have the stipulated typed
converses. Semantic CCO is for finite typed partial diagrams with specified
diversity edges and colour-preserving homomorphisms. Formal vertices without
a specified edge may have the same image. No infinitude or SAP is needed.

Completeness and homogeneity identify each named atomic binary relation
with one actual ordered-pair orbit. For a same-sort identity pair this uses
one-point transitivity; for a diversity pair it uses a two-point partial
isomorphism. Thus an invariant relation contains either all or none of any
atom. Work either with invariant sets of ordered pairs, or their sets of
atoms, with this equivalence proved once.

If a nonempty invariant relation R goes from sort i to sort j, choose one
pair (r,s) in R. To find a predecessor of an arbitrary b in sort j, use an
automorphism sending s to b. To find a successor of an arbitrary a in sort
i, send r to a. Consequently every ball of a nonempty invariant relation
at an actual centre is nonempty. Compatible nonempty invariant relations
have a nonempty product. More strongly, composing a typed universal
relation with a compatible nonempty invariant relation on either side is
the appropriate typed universal relation. These statements use the relevant
original-sort transitivity, not homogeneity of any quotient.

For typed relations A:i→j and B:j→k, composition is
(A;B)(x,z) iff there exists y with A(x,y) and B(y,z). Associativity,
monotonicity, identity laws and (A;B)ᵒᵖ=Bᵒᵖ;Aᵒᵖ follow by rearranging
witnesses. If a:i→j and c:i→k are atoms and B:j→k is invariant, then
c⊆a;B iff a∩(c;Bᵒᵖ) is nonempty. One witnessed pair gives the entire
output atom by invariance. This is the typed Peirce rule used below.

Only in the one-original-sort symmetric setting is every invariant binary
relation symmetric. Its product is invariant, hence symmetric too, so
A;B=(A;B)ᵒᵖ=B;A. This commutation is not used for mixed original sorts.
Commuting invariant equivalences E,H satisfy E;H=E∨H: the product is a
reflexive symmetric transitive relation containing both, and every
equivalence containing E and H contains their product.

## N02: Words, presentations and finite diagrams

A typed word records its successive sorts and atomic edges. Its profile is
the actual endpoint relation of a walk spelling that word. Walks need not
be injective. The empty word is allowed only from a sort to itself and has
profile Id, whereas an empty list of restrictions on a pair of sorts has
intersection Top. Delete identity letters from a word without changing its
profile. Reversal with converses gives the converse profile; concatenation
gives relational composition. A reduced word can still have Id among its
outputs: deleting identity *letters* does not delete identity *outputs*.

Separate `ExactPresentation` (a finite list of typed words) from
`NonemptyExactRelation` (its evaluated intersection plus a nonemptiness
proof). Different presentations can have the same evaluation. An exact
equivalence is an invariant equivalence with a presentation whose
evaluation is nonempty.
The meet operation on nonempty exact relations is conditional on its
result being nonempty. A nonempty indexing set does not ensure that.

When using CCO, build a finite simple typed graph explicitly. Each private
path has new internal vertices used in that path only. Delete equality
letters first. If a zero-length restriction remains, handle the identity
case before making a graph with two distinct terminals. For duplicate
length-one paths between fixed terminals, prove the atoms equal before
merging the edges. Longer paths have disjoint interiors even when their
colour words agree. No parallel-edge cycles or artificial equality edges
are introduced.

## N03: Word Helly and nonempty exact meets

Given finitely many profiles of one endpoint type, assume each is nonempty
and any two distinct profiles intersect. With no profiles the intersection
is Top, which is nonempty; with one profile use its witness. If an
identity-only word occurs, pairwise intersection puts the unique identity
atom in every profile. It gives the total intersection directly.

Otherwise make a theta with two terminals and one reduced private path for
each profile. Duplicate length-one paths must have the same atomic colour
by pairwise intersection and are merged. Every simple cycle consists of
exactly two distinct terminal-to-terminal paths. This follows because every
internal vertex has degree two, and a simple cycle cannot revisit either
terminal. A single remaining path produces no cycle.

For either pair of paths choose an atom in their profile intersection.
If it is diversity, two-point homogeneity transports both word walks to
the same actual ordered pair of that atom. If it is identity, one-point
transitivity transports both to the same based loop. Map the two private
interiors independently. This realizes the chosen simple cycle. CCO now
gives a homomorphism of the whole theta, whose endpoint pair belongs to
every original profile. Its endpoints are allowed to coincide.

For finitely many nonempty exact menus with pairwise nonempty
intersections, flatten all presentations. Two constituent words from one
menu have a common point in that menu; constituent words from different
menus have a common point in the corresponding menu intersection. Word
Helly supplies a common atom for all menus. Empty presentations contribute
no restrictions. Reversing presentations proves converse closure; joining
lists proves closure under a meet whose result is nonempty.

## N04: Convolution and saturation

Let D=⋂α Pα:i→j and F=⋂β Qβ:j→k be nonempty exact menus. The inclusion
D;F⊆⋂αβ(Pα;Qβ) follows by monotonicity. If either list is empty, the
top-absorption result in N01 proves equality directly.

Otherwise fix an atom c in the right-hand side. Consider the word profiles
Pα and c;Qβᵒᵖ, all of type i→j. The Pα have a common witness in D.
Choose an atom b⊆F. The nonempty product c;bᵒᵖ is contained in every
c;Qβᵒᵖ, so the second group meets pairwise as well. Every cross pair
meets by typed Peirce and c⊆Pα;Qβ. Word Helly gives an atom a contained
in D and every c;Qβᵒᵖ. Now apply word Helly to all Qβ and the one word
aᵒᵖ;c. Peirce supplies the cross intersections, and F supplies the
intersections among the Qβ. Obtain b⊆F with c⊆a;b, proving c⊆D;F.
Concatenating the defining words supplies an exact presentation of D;F;
N01 supplies nonemptiness.

Flattening presentations proves distribution over a finite exact meet
whose evaluated intersection is nonempty. Thus, for invariant exact
equivalences E,H and nonempty D=⋂r Dr,
E;D;H=⋂r(E;Dr;H). This uses the distribution law twice, with its
nonemptiness premises verified at each intermediate step. For no Dr,
both sides are Top. It is false that saturation preserves arbitrary
empty intersections; the controls contain a concrete witness.

## N05: Heterogeneous ball Helly and anchoring

Use B_D(b)={x:D(x,b)}, with D from the target sort u to the centre's
sort. Directly unpacking composition gives
B_D(b)∩B_F(c)≠∅ iff (b,c)∈Dᵒᵖ;F. This identity needs neither exactness
nor CCO, and determines the orientation used throughout.

For a finite family of nonempty exact balls, n=0 is nonemptiness of sort
u and n=1 is seriality. First delete all identity letters in its word
presentations. If any menu now has an empty-word restriction, its
nonempty evaluation is Id and its ball is the singleton consisting of its
centre. Pairwise intersections then put that point in every ball. Discard
Top restrictions and attach private paths for the remaining reduced words
from one formal target z to the centres. Distinct *values* of centres
give distinct marked vertices; two occurrences of the same actual centre
use the same vertex. Retain the complete actual diagram on these values.

Two length-one constraints to the same value have the same colour: use
one ball witness if both come from one menu, or a witness of the two-ball
intersection if they come from different menus. Merge the edges. A simple
cycle avoiding z lies in the actual centre diagram. A cycle through z
uses exactly two private paths and a simple route in that diagram. The
route has length zero when the two paths end at the same centre. Choose a
witness of the two corresponding balls (of the single ball when their
indices agree), realize both chosen words with these actual endpoints,
and retain the actual centre route. This realizes the cycle. It does not
require a witness of the whole family before CCO is applied.

In any CCO homomorphism, the marked centre diagram embeds: its distinct
same-sort vertices have specified irreflexive colours, and different sorts
remain disjoint. Its image has exactly the original complete atomic
diagram. Homogeneity extends the inverse finite centre isomorphism to an
automorphism. Composing brings every centre back to its prescribed value;
the image of z is the required common point. If no centres remain, choose
any target point. All these constructions allow the target image to equal
a centre when no specified diversity edge prevents it.

## N06: Actual quotient orbitals, colours and mixed joins

For invariant equivalences J on original sort s and K on t, take actual
classes and the induced action of G=Aut(N). If a is the original atomic
orbital of (x,y), the full pullback of G·([x]_J,[y]_K) is J;a;K.
In one direction transport the original pair by g and then change
representatives within its classes. Conversely, witnesses x',y' for
r J x', x' a y', y' K q give an automorphism carrying (x,y) to
(x',y'), hence the desired pair of classes. This proves the orbit claim,
not just invariance or saturation. Distinct such saturated pullbacks are
equal or disjoint and exhaust the real pair space.

For exact J,K the pullback is nonempty exact by convolution. It is
(J,K)-saturated: J;(J;a;K);K=J;a;K. Consequently *every* representative
pair of a quotient pair in that orbit satisfies every word of a chosen
exact presentation. It need not have original colour a. In general an
invariant saturated relation descends to a union of quotient pair orbits;
if it intersects one such orbit it contains that entire orbit. Both
invariance and saturation are used in this last inference.

In the one-original-sort symmetric case, E;a;E=E;a by commutation and
idempotence. For finitely many exact E_i, m≥1, their meet K contains Id
and is exact. Nonempty meet-distribution gives
⋂i(E_i;a;E_i)=K;a;K. Choosing a from a representative of one K-pair
therefore shows that all its projected E_i pair orbitals determine its
K pair orbital. This includes all logical diagonals. It makes no tuple
realization assertion. No reconstruction of original fine colours from an
empty family is asserted.

For one-sort invariant equivalences E,H (exactness is unnecessary for
this algebraic step), their join J=E;H satisfies
E;a;H=J;a;J=J;a. In particular if E≤H, the mixed pair orbital is determined
by the H-projected pair. For partial maps, require that the domains of
their induced J-projections are covered by one common partial
isomorphism, with both maps agreeing with it. It then preserves every
mixed pair, including pairs whose original domains did not meet.
Agreement merely on an overlap is insufficient. The nested source lemma
spells out the needed domain coverage for its coarser map.

## N07: Extending a finite joint map by a real point

Let f be a finite partial isomorphism in the full actual quotient orbital
language, with the original real sorts included as Id quotients. Take
x of original sort u outside its real domain. For each displayed
parameter d_i of sort N_t/J_i, choose c_i∈d_i and let a_i be the
original atomic orbital of (x,c_i). The mixed orbital of (x,d_i) has
pullback D_i=a_i;J_i; this is a nonempty exact relation, right-saturated
by J_i. Different choices of c_i describe the same mixed orbital.

Choose b_i∈f(d_i). Pair-orbital preservation gives, for each distinct
parameter pair, an original automorphism taking both parameters to their
f-images simultaneously. Its image of x belongs to both B_Di(b_i) and
B_Dj(b_j), using right saturation. For a single parameter use seriality;
for none use a target point. Heterogeneous exact-ball Helly gives a y
meeting every requirement. Preservation of the entire named pair orbital,
not preservation of some chosen subset of colours, is the input here.

For every old real parameter z of sort u, x≠z, so their orbital is
irreflexive. The constraint for z has J_i=Id and forces y≠f(z).
Thus the enlarged map is injective. Same-sort unary data consist only of
the named sort, so the diagonal orbital of (x,x) is automatically
preserved. Every pair involving x has its specified mixed orbital, while
old pairs were already preserved. The enlarged map is therefore a finite
partial isomorphism. This proves extension without choosing a global
quotient section or making a fresh-point avoidance assumption.

## N08: Back-and-forth, quotient anchoring and unary enrichment

Choose a sequence covering the countable total real universe; a finite
nonempty universe can be covered with repetitions. Alternately extend a
joint map to include the next real point in its domain and apply the same
extension to its inverse to include the next point in its range. Skip a
point already present. Every stage is finite and extends the preceding
map. Initially displayed quotient parameters remain in the joint map at
every stage; it is not necessary to enumerate all quotient classes.

The union on real points is a sort-preserving bijection preserving every
original pair atom, hence an automorphism g of the original binary source.
For an initial parameter d=[c]_J, the mixed orbital of (c,d) is precisely
membership in that class: its pullback is J. Eventually c is added, so
preserving this orbital forces [g(c)]_J=f(d). This proves that one g
induces the whole initial finite joint map. Lifts chosen in different
runs need not be coherent, and no group section follows.

An actual equivariant unary function between the displayed sorts is
preserved by every induced g. Forgetting unary symbols from an
isomorphism of finite functionally closed substructures leaves a finite
partial isomorphism on exactly the same vertices of the full binary
reduct. The lifting theorem supplies one g, and equivariance supplies
preservation of every added unary function. No arbitrary representatives
are adjoined to the finite domain, and no claim of SAP or local finiteness
of all unary closures is needed for this conclusion.

## N09: Triangle realization and AP of the quotient age

Here the source result is for the one-original-sort symmetric M and its
finitely many exact quotients. A legal finite complete typed diagram has
all subdiagrams on at most three vertices in the actual age, including
valid singleton sorts, distinct same-sort diversity pairs, and cross-sort
pair orbitals. This convention handles the 0/1/2-vertex base cases.

Inductively suppose earlier vertices d_i of sorts M/J_i are realized and
choose representatives y_i. For a new vertex of sort M/K let the required
edge pullbacks be R_i=K;a_i;J_i. Each R_i is nonempty exact. A legal
triangle with earlier vertices i,j gives one quotient pair in their
prescribed orbital whose representative pair lies in R_iᵒᵖ;R_j.
This product is invariant and (J_i,J_j)-saturated. It therefore contains
the entire earlier quotient pair orbital, not only the pair chosen in
the triangle witness. In particular the already fixed (y_i,y_j) belongs
to it. The balls B_Ri(y_i) meet pairwise and exact-ball Helly provides a
new representative y. Its K-class has every required orbital. A
same-sort diversity edge excludes its coincidence with earlier K-classes;
different quotient sorts are disjoint tagged carriers even if their real
representatives coincide. Seriality handles a one-vertex old diagram.

This realizes every legal diagram, but does not assert strong amalgamation.
For AP, embed two actual finite joint structures into M_E. Use joint
homogeneity to align the embeddings of their common finite induced base,
then take their finite union inside M_E. This is the usual age AP
argument. It does not require a triangle-level amalgam to be constructed
before the two embeddings are aligned. Homogeneity similarly permits a
realization of a legal diagram to fix a prescribed already realized
induced subdiagram.

Each individual quotient has a nonempty countable carrier and is
transitive under the induced original action. Every quotient pair orbit
has an original atomic representative, so there are finitely many such
orbits. Same-sort quotient orbitals are symmetric because their original
pullbacks are symmetric. Restrict joint lifting to a partial map in this
one quotient sort to obtain homogeneity. Restrict the preceding age
properties and the CCO argument below to this sort to recover the standing
single-source properties.

## N10: Semantic CCO of the actual quotient age

Replace each specified typed edge by private reduced word paths for an
exact presentation of its saturated pullback. An empty presentation gives
Top and contributes no paths. If an edge pullback were contained in Id,
left and right saturation would force both equivalences to be Id, and
its output would be real equality. Such an edge cannot connect distinct
vertices of a legal specified diversity diagram. Thus no edge presentation
contains a zero-length restriction. Suppress identity letters first.

Multiple length-one paths belonging to one edge have the same atom, since
the pullback is nonempty; merge them. Paths replacing different edges
cannot produce a duplicate edge between the same marked pair in a simple
partial diagram. Every internal vertex has degree two. Hence a simple raw
cycle uses whole private paths and either visits exactly two marked
vertices (two paths for one edge) or at least three distinct marked
vertices (a specified simple cycle of the typed diagram).

In the second case choose the hypothesized typed cycle homomorphism; in
the first choose any actual pair from the edge orbital. Fix arbitrary
real representatives of the marked images. Saturation puts every
endpoint pair in every profile of that edge's presentation. Realize each
private path with those endpoints; their internal vertices are disjoint,
so these homomorphisms agree wherever they meet. This is the
representative-independent cycle-lifting argument; it uses no joint
lifting theorem and no pre-existing CCO on quotient sorts.

Apply real semantic CCO to the expanded raw diagram. Each marked pair is
in every profile replacing its typed edge, hence in the saturated orbital
pullback. Top edges are automatic. Project each marked image to its tagged
quotient sort to obtain a typed homomorphism of the original diagram.
Unjoined vertices may coincide. This proves the quotient CCO assertion
independently of its AP assertion.

## N11: Implementation boundaries and feedback to the articles

The finite graph constructions and the countable back-and-forth are real
proof work to implement. An acyclic diagram or a checked finite model
does not discharge them. The module tasks split relation/word evaluation,
private-path graph combinatorics, CCO use, quotient actions and finite-map
back-and-forth into separate units. The exact Lean APIs and import files
remain to be chosen by compiling them in the eventual Lean project.

This pass found no required change to a theorem's mathematical hypotheses
or conclusion. Three wording clarifications are recorded for a later human
article pass: nonempty-result meets, invariant saturated orbital descent,
and legality on at most three vertices. They already have the intended
meaning in the proofs; no new numbered result belongs in the article for
these details. This file and the machine-readable feedback ledger retain
their locations so that useful explanations can be carried back later.
