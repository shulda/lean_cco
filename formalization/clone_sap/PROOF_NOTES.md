# B045 — pure-clone SAPification and the symmetric palette lattice

Frozen source `490c3f36d85db5a0b3ced0598e6c431825254ec5`.
Eight definitions, 36 human proof claims, TWO selected new Ramsey results,
one equation JC and five tasks. There are NO imports or external theorem
providers. This is mathematical preparation, not compiled Lean or a global
Ramsey certificate. The palette result is independent of the clone proof.

## N01: Actual clones, owner quotients and homogeneous extension

**D01–D03; C01–C05.** The carrier is Q x N with the old unary sort
labels pulled back. Distinct clones of one old owner have new diversity
colour c (one c_a for each original sort); pairs with different owners
retain their old Q colour. Logical equality is not a diversity atom.
Thus K=Id union c is exactly equality of owners. Quotienting a finite
actual induced clone object gives the actual finite complete diagram on
its owner set in Q. Old colours between K-classes are independent of
representative indices. Any induced clone embedding induces an induced
embedding of its owner diagram.

A finite clone partial isomorphism preserves K and hence induces an old
partial isomorphism. Extend it to alpha in Aut(Q) by original homogeneity.
For each owner q, extend the finite injection prescribed on its clone
indices to a bijection N→N in the fibre over alpha(q). The choices in
different fibres are independent; combining them with alpha extends the
original partial isomorphism to a clone automorphism. Conversely every
clone automorphism preserves definable K and projects to an old Q
automorphism. No section or preferred clone is required.

These arguments do not use old AP, CCO or triangle-definedness. Finite
nonempty Q is allowed: only its clone fibres must be infinite.

## N02: Transfer of triangle-definedness

**D04; C06–C10.** A locally legal COMPLETE clone diagram uses actual
singleton/pair types as well as actual permitted triples. This convention
is essential for diagrams with fewer than three vertices. The actual
clone triangle table forces two c-edges to have a third c-edge, so Id
union c is an equivalence. With a c-related pair and an external point,
a permitted c,a,b triangle forces the two old incident colours equal in
their typed orientation. Therefore all old labels between two different
clone classes are uniform.

Collapse these classes. Every quotient triangle has actual Q colours,
and its three representatives form a permitted clone triangle with three
distinct owners, so it is an actual Q triangle. Unary/pair legality also
descends. Old triangle-definedness embeds the complete quotient into Q.
Choose distinct natural-number indices for the finitely many vertices
over each owner; this realizes the original complete clone diagram
inducedly. The converse triangle-definedness implication is also valid:
put a locally legal complete old diagram upstairs using only old atoms.
Any induced clone realization then has distinct owners at all distinct
pairs, so projection gives its induced Q realization. This converse is
internal support, not another numbered source result.

## N03: Ordinary owner AP yields strong real clone AP

**C11–C13.** Given a finite clone span A→B,C, quotient by K. Its
owner-base diagram embeds inducedly into both owner leg diagrams, even
when a leg has additional clones whose owner is already represented in
A. Apply ORDINARY old AP. It may identify off-base owners from opposite
legs; it cannot identify different owners within one leg, because each
old leg map is an induced embedding.

Take the formal real union of B and C over their actual common real A.
Above each owner in the amalgam assign different fresh indices to all
distinct vertices of this formal union, keeping exactly the real base
identifications. Infinite fibres provide enough indices. Inside each leg
all old colours survive, and its same-owner pairs remain distinct c-pairs.
Both leg maps are induced embeddings. Their real image intersection is
exactly A, giving SAP. Cross-leg relations are inherited from the actual
clone structure, so no free-amalgamation assertion is made. Old SAP is
not used.

## N04: c-components, simple-cycle obstructions and HOM CCO

**D05/D06; C14–C22.** Let P be a finite typed clone diversity partial
graph with every specified simple cycle clone-homomorphic. Its c-edge
components, including isolated vertices, each lie in one original sort.
The old CCO theorem need not be extended by a new equality-labelled
black box: construct a genuine old diversity quotient directly.

First, an OLD diversity edge cannot have both endpoints in one c-component.
A shortest c-path between those endpoints plus that old edge is a simple
cycle. The graph has one atom per pair, so the c-path has length at least
two; this is a genuine cycle of length at least three. In any clone
homomorphism the c-path has one old owner, while the old diversity edge
requires distinct owners. This contradicts cycle feasibility.

Second, old edges between two different components cannot have conflicting
labels when both are oriented from the first component to the second.
Join their respective endpoints by simple c-paths inside the two components.
These paths have disjoint vertex sets. Together with the two old edges
they form a simple cycle. One connecting path may have length zero when
its endpoints coincide; both cannot have length zero for genuinely
different conflicting edges of a simple partial graph. A clone homomorphism
of the cycle would make both old colours hold on the same ordered owner
pair, contradicting atomic exclusivity. Thus duplicate quotient edges
agree.

Contract the components and deduplicate their old edges. By the preceding
two arguments this is a simple typed OLD diversity partial graph, retaining
all isolated component vertices. To check one of its simple cycles,
choose an original old edge representing each quotient edge. Within each
visited c-component join the incoming and outgoing endpoints by a simple
c-path, allowing length zero. Each component occurs once around the quotient
cycle, so these paths have disjoint interiors. The resulting clone cycle
is SIMPLE. Its assumed clone homomorphism, projected to owners, yields an
old homomorphism of the quotient cycle.

Now ORIGINAL Q HOM CCO supplies a whole owner solution of the quotient.
Nonadjacent quotient vertices may collide. Give all original formal real
vertices distinct indices within each owner fibre selected by this
solution. Every specified c-edge now joins distinct clones of one owner;
every specified old diversity edge keeps its old Q atom. This gives a
whole clone homomorphism, indeed one injective on formal real vertices.
It is a homomorphism of the partial specified-edge diagram, not an assertion
that missing edges are reflected. No old AP, SAP, triangle-definedness,
collision-unfolding or equality-extended CCO theorem was used.

Conversely, assume clone HOM CCO and take an old partial diagram with all
simple cycles Q-feasible. Regard it upstairs using only old atoms. Each
cycle solution lifts by choosing distinct clone indices over its old
owner solution. The cycles can use different lifts. Clone CCO gives a
whole upstairs homomorphism, whose owner projection is a whole Q solution.

## N05: The exact represented clone kernel and source assembly

**C23–C26.** Every two-step c-walk stays in one owner fibre, so c;c⊆K.
For any two clone endpoints in one fibre choose a third clone different
from both; it witnesses c;c. For equal endpoints just one exclusion is
needed. Therefore c;c=K=Id union c. This is a positive FULL represented
word profile, with old logical equality as a possible OUTPUT. No equality
is added as a diversity edge. The owner quotient is canonically the actual
old Q. For several original sorts apply the same construction to each
sort-specific c_a and K_a, retaining all mixed old colours.

Together N01, N02, N03, N04 and this exact-kernel calculation prove the
pure-clone SAPification source result. Each branch has its own metadata
firewall: homogeneity/kernel calculations do not require CCO; SAP uses
old ordinary AP only; triangle transfer uses old triangle-definedness;
clone CCO uses old HOM CCO only. The combined export assumes all the
stated original source premises, without importing a later Ramsey theorem.

## N06: The independent palette lattice and the endpoint swap

**D07/D08; C27–C33.** Fix ONE actual homogeneous named transitive
symmetric sort M with finite occurring diversity palette L. Complete
same-colour two-point maps extend to full automorphisms; hence each named
colour is exactly one full pair orbital, and the diagonal is one orbit
by transitivity. Any invariant relation is a union of these finitely many
named orbitals, and each union is parameter-free definable. An equivalence
contains the diagonal and therefore equals precisely one E_X, for X⊆L.
Uniqueness concerns ACTUAL occurring atoms, not unused syntactic names.
Thus this proves the stated parameter-free definable correspondence and
also its invariant-relation strengthening as internal support. Lambda
is finite, with equality/top and meets given by palette intersections.

For invariant equivalences E,F and x E y F z, degenerate cases reverse
the composition immediately: if x=y use z as the F;E witness, if y=z
use x, and if x=z use x. Otherwise x,y,z are distinct. The complete
induced map swapping x,z is an isomorphism because their same-sort atom
is symmetric. Extend it to a full automorphism g; put w=g(y). We get
z E w F x, hence x F w E z. Exchange E,F to conclude E;F=F;E.
This uses the ACTUAL homogeneous structure. It assumes no abstract
triangle table, CCO, AP/SAP, countability or clone construction, and
requires no separately bound Fraisse one-point-extension theorem.

The full represented product R=E;F is reflexive, symmetric because
R^op=F;E=R, and transitive because R;R=E;(F;E);F=E;E;F;F=R.
It contains both E,F and is contained in every equivalence containing
them, so it is their least upper equivalence. It is invariant and hence
has its unique palette Z=X join Y. Together with literal intersection
for meets this proves the finite lattice and JC equation. Join is not
asserted to be set union of palettes. Composition includes logical
diagonals and is not strong diversity-only multiplication. Empty L
correctly gives the singleton equality/top lattice.

## N07: Boundary examples and finite diagnostic scope

**C34–C36.** Symmetry matters to palette permutability. As an outside-
scope example take the regular left action on S3 and name every directed
difference R_g(x,y) iff x^{-1}y=g. It is homogeneous: every nonempty
partial isomorphism agrees with one left translation. For H=<(12)> and
J=<(23)>, invariant equivalences E_H,E_J compose according to HJ,JH,
which differ. This makes no claim of symmetric colours or CCO for S3.

A two-clone fibre has c;c=Id, not K. At least three indices suffice for
the bounded c;c kernel identity, while arbitrarily many indices are used
for the general strong-amalgam and whole-diagram construction. For each
fixed finite fibre size m>=2, two full c-fibre extensions over one real
point cannot amalgamate strongly: they would require 2m-1 clones of that
same owner. The m=1 construction has no realized c and is simply Q; it
has SAP only when Q does, so no universal m=1 failure is asserted.

The controls use sufficiently large finite clone windows for the graphs
and spans ACTUALLY tested, not as claimed unbounded SAP/CCO sources.
They independently compare finite homomorphism search with simple-cycle
feasibility/component contraction, check a genuine ordinary-owner AP
collision becomes real strong amalgamation, test finite partial isomorphism
extension, full represented kernel products and palette lattice products.
The old two-point owner Q is AP but not SAP and has HOM CCO by bipartiteness;
its infinite clone cover is the mathematical example. Finite windows do
not prove the unbounded theorems. Singleton owner sources, empty diagrams,
isolated vertices and zero old diversity palettes are retained. Every
used original sort is nonempty. The source TeX is unchanged; no external
provider or compiled Lean certification is introduced.
