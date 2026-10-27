# SIR: proof details for a receiving Lean project

This module covers the eight results in the two `stationary_independence`
source files. It supplies preparation, not Lean code. Follow the shared
[receiving-project work order](../HANDOFF.md). Positive construction,
finite-global obstruction and the direct relative example are separate
proof branches with different hypotheses.

## N01: Finite sets, named parameters and the conditional constructor

For arbitrary finite A,B,C use A∪C and B∪C as the two displayed sides.
Their intersection is exactly C iff A∩B⊆C. Cross endpoints belong to
A\C and B\C and are distinct when this condition holds. Establish these
facts before forming their strong base-path menus. Empty sides and sides
contained in C have no cross requirements.

Use pointwise finite types: an induced isomorphism f:A∪C→A'∪C must fix
every c∈C, and a type over B∪C fixes every parameter there. A setwise
permutation of the parameters is not such a type equivalence. Export the
stationarity proof for each prescribed f, rather than only the assertion
that some map of unenumerated sets exists.

The conditional positive constructor consumes actual SAP, the original
strong exact calculus, triangle fullness, homogeneity and ONE joint
hereditary PC-preserving selector h. Once these are supplied, its proof
uses neither NR2, CCO nor countability again. For the source headline,
CCO supplies the exact/triangle interfaces and full sortwise NR2 supplies
h through the STRONG module. Keep these two levels separate in Lean.
The conditional DAG uses explicit interface parameters, not applications
of the theorems deriving those interfaces. The source-instantiation step
discharges these parameters using I01–I03.

## N02: Base-path menus and a complete free-span PC network

Take disjoint formal copies of finite complete A,B over C, with A∩B=C.
For a∈A\C,b∈B\C let
D_C(a,b)=⋂c∈C ({col(a,c)}*{col(c,b)}), using diversity Top for C=∅.
Each factor is original strong exact. SAP gives one actual strong
amalgam; its cross atom lies in every factor. Thus the evaluated
intersection is nonempty and exact. This witness is used only to prove
nonemptiness and support, never to define the chosen output.

Put singleton domains on old pairs and D_C on cross pairs. Old triples
are legal. A triple (a,c,b) through the base satisfies D_C⊆u*v by
definition; its two singleton coordinates have support from the SAP
witness. For two left vertices a,a' and a right b, let p=col(a,a').
Each old triangle through c gives
col(a,c)∈{p}*{col(a',c)}. Associativity, monotonicity and distribution
over the nonempty exact meet yield D_C(a,b)⊆{p}*D_C(a',b).
Interchanging a,a' gives the correctly typed converse inclusion.
A strong amalgam witnesses p in the product of the two cross domains,
giving the remaining singleton coordinate. The other orientation follows
by converse. At C=∅ these arguments use strong Top absorption. All three
coordinates hold even for repeated sort names; actual vertices are distinct.

## N03: Selecting an amalgam and the triangle-fullness bridge

The conservative selector fixes atomic singletons. Apply it to every
domain of the free-span network. Each triple's singleton outputs form
an actual legal triangle by all-coordinate PC preservation. The complete
output therefore belongs to the age by triangle fullness. Converse
compatibility makes the output a well-defined symmetric typed complete
structure on the literal disjoint union over C.

The source headline does not separately assume triangle-definedness.
Its bridge is the imported `lem:cco-triangle-fullness`. The short proof
works with named sorts: for each specified cycle, triangulate it by a fan
from one of its vertices; repeatedly amalgamate the actual fan triangles
over their common complete edge. AP preserves the sort tags and realizes
the boundary cycle homomorphically. Thus every cycle of the triangle-legal
complete diagram has a homomorphism. CCO realizes the entire diagram.
Because every distinct pair has a specified diversity edge, that final
homomorphism is injective. Boundary diagrams on at most two vertices are
required to be legal as well. No quotient or unary-function variant is
being asserted.

For a conditional constructor, triangle fullness can be an explicit
interface; the receiving project must connect that interface to this
source bridge when instantiating the headline. Its proof snapshot is
included so that this is a small named task rather than a hidden premise.

## N04: Naturality has an onto-base condition

Suppose embeddings f_A:A→A', f_B:B→B' agree on C and take C ONTO the
entire designated target base C'=A'∩B'. The target factor embeddings
may add vertices. For each source cross pair, every target base point is
the image of a source base point, so its full target menu equals the
source menu, including the tagged endpoint sorts. The selected atom is
therefore unchanged. This proves naturality of the selected amalgam for
these embeddings; fixed common bases are a special case.

A nonsurjective map of bases is not covered. In the three-level
ultrametric palette, PC({3},Top,Top) forces h(Top)=3, while conservativity
gives h({1})=1. Two singleton factors over the empty base receive cross
colour 3. Embed those factors into A'={a,c},B'={b,c} over the larger
base {c}, with both incident colours 1. The new cross menu is {1} and
its selected colour is 1. Hence the union of factor embeddings is not
an embedding of the selected amalgams.

This makes precise the source's explicit exclusion of arbitrary base
enlargement. The feedback ledger records the needed interpretation of
“embeddings of the entire span”: onto the designated base, not merely
intersection preservation on the two image factors.

## N05: Invariance, symmetry, existence and restriction

Normalize finite sets as in N01 and require A∩B⊆C and every cross
atom equal to h(D_C). Automorphisms preserve named sorts and literal
colours, so they preserve menus and the fixed h-values. The formula
D_C(b,a)=D_C(a,b)ᵒᵖ and converse compatibility give symmetry.

For existence, copy A∪C formally over C disjoint from B∪C outside C
and construct the selected finite amalgam. It lies in the age. Embed it
into U and align its B∪C copy with the fixed actual one by homogeneity.
This yields an independent copy of A of the prescribed type over C.
No algebraic closure of the base is assumed. This finite extension over
a fixed copy is a consequence of age membership and homogeneity, not a
new Fraïssé uniqueness theorem or countable construction.

Dropping vertices on either side leaves its remaining base-path menus
and selected cross colours unchanged, giving restriction monotonicity.
Base monotonicity is the separate forward transitivity argument below;
it is not justified merely by dropping vertices.

## N06: Base enlargement and forward transitivity

For endpoints outside B∪C, split the index set of base constraints to get
D_(B∪C)(a,d)=D_C(a,d)∩⋂b∈B\C ({col(a,b)}*{col(b,d)}).
Each actual intervening triangle uses three distinct vertices.

Assume A↓_C(B∪D). Restriction gives A↓_C B. Its overlap condition
also gives the overlap needed over B∪C. For every new cross pair a,d,
the actual atom col(a,d)=h(D_C(a,d)) satisfies each extra constraint
through b. Thus it belongs to the enlarged intersection, proving its
nonemptiness as well. Exact meet closure makes it an original exact
submenu of D_C. Survivor heredity then gives
h(D_(B∪C)(a,d))=h(D_C(a,d))=col(a,d).
This proves A↓_(B∪C)D, including C=∅ or B\C=∅.

## N07: Reverse transitivity and arbitrary overlaps

Assume A↓_C B and A↓_(B∪C)D. Set identities first give
A∩B⊆C and A∩D⊆B∪C, hence A∩(B∪D)⊆C. This legitimizes
forming the free span of A∪C and B∪D∪C before its independence
has been proved. In particular a∈A\C is outside B∪C.

Colours to B are already selected. For d∈D\(B∪C) put
q=h(D_C(a,d)). For every b∈B\C the free-span PC network has the
triple D_C(a,b), {col(b,d)}, D_C(a,d). Apply h to this triple. It
fixes the literal singleton, and A↓_C B identifies h(D_C(a,b))
with col(a,b). Therefore q lies in {col(a,b)}*{col(b,d)}.
For c∈C its membership follows from D_C itself. It consequently
survives every constraint defining D_(B∪C)(a,d), which is nonempty
exact and contained in D_C(a,d). Heredity gives its selected value q;
the second independence hypothesis identifies col(a,d) with that value.
This proves A↓_C(B∪D).

The two directions give the complete transitivity equivalence on arbitrary
finite A,B,C,D after normalization. Reverse transitivity uses BOTH all-PC
preservation and survivor heredity. Conservativity alone, or either of
those two properties on its own, does not justify the calculation.

## N08: Stationarity for a prescribed pointwise map

Let f:A∪C≅A'∪C fix C pointwise, and assume both sides independent
from B over C. The normalized sides meet B∪C only inside C. Thus
f∪id_(B∪C) is well-defined and injective; its range is A'∪B∪C.
Old pairs are preserved by f or the identity. For a cross pair,
col(f(a),c)=col(a,c) for each c∈C, while col(c,b) is fixed.
The two tagged base-path menus agree and therefore have the same
h-value. Independence says these values are the actual cross atoms.
Consequently the union is an induced isomorphism. Homogeneity extends
this particular map to an automorphism fixing B∪C pointwise.

This proves stationarity in a form suitable for tuple types or finite
embeddings. For C=∅ all cross menus are Top but remain tagged by the
named sorts; no permutation covariance of h is needed. Empty A or B
reduces to the appropriate old induced map. Combining N05–N08 gives
the conditional SIR constructor, then the imported HS theorem gives the
source NR2 headline. No-finite-relative-index implies NR2, not conversely.

## N09: Original-language global quotient obstructions

First prove an abstract symmetry obstruction: suppose an invariant
equivalence has two classes and some automorphism σ preserves a finite
parameter set B meeting both classes setwise while swapping both classes. Singleton existence
over ∅ gives x↓_∅B. Invariance gives σx↓_∅B; x and σx have the same
empty-base type. Stationarity would make their types over the POINTWISE
named B equal. A parameter in B distinguishes their E-classes, contradiction.

In the standing one-sort symmetric complete diversity language, two
representatives a₀,a₁ have identical singleton diagrams and their swap
is an induced two-point partial isomorphism. Homogeneity produces such
a σ for B={a₀,a₁}. State this singleton/transitivity premise when exporting
the isolated lemma: allowing diagonal predicates that name sheets would
invalidate the inference from symmetry alone.

For a proper invariant E of finite global index, the interval [E,Top]
is finite: its equivalences induce partitions of the finite set M/E.
Choose a maximal proper F in that interval. It is a cover below Top
in the FULL invariant lattice. The separate Hasse provider gives
[Top:F]=2. Every invariant binary relation is a finite union of actual
named pair orbitals (and possibly equality), hence 0-definable in the
original language. Apply the two-class obstruction without adding sheet
names. Only the cover-index-two part of Hasse is needed for this step.

The Hasse proof itself is NOT expanded by this module. Its provider uses
the original orbital-parity theorem and the high-girth/high-chromatic
graph input. Include its source snapshot and leave it as a named upstream
proof obligation for the receiving project. No SAP, quotient CCO,
quotient homogeneity or exactness premise is silently substituted.

## N10: A direct relative-two-sheet model

Take U=ℕ×{0,1}×ℕ. F means equal first coordinate; E means equal first
and second coordinates. Name only the diversity atoms e=E\Id,
d=F\E,n=Top\F, not the coordinates or individual sheets. Its finite
age consists of nested equivalences with AT MOST two represented
E-classes per represented F-class. A finite object need not show both.

Parent permutations, independent sheet swaps in each parent, and fibre
permutations extend every finite induced partial isomorphism. For SAP,
keep parents absent from the base separate across extensions; in a
represented parent align the two sheets with the base, then retain all
off-base points as distinct. Infinite fibres permit this without collision.
This explicitly gives the actual original-language homogeneous SAP source.

For CCO, e/d edges form signed components with parity 0/1. An inconsistent
parity assignment yields an odd-parity simple cycle. An n-edge within
one such component closes a shortest e/d path to a forbidden simple
cycle. If neither occurs, assign a fresh parent per component, solve
the sheet parity, and choose distinct points in the relevant infinite
fibres. This realizes the diagram. Its F:E interval has index two,
so the model VIOLATES NR2; do not invoke the selector sufficient condition.

## N11: SIR on the direct model and the grid firewall

Declare independence when (A\C)∩(B\C)=∅ and no parent disjoint from
C meets both A\C and B\C. This formula is unchanged by adjoining C
to both sides. Existence moves unanchored parents to fresh ones, keeps
the required sheets in parents represented by C, and picks fresh points.
Invariance and symmetry follow directly.

For forward transitivity, a parent disjoint from B∪C is disjoint from
C, so a violation at the larger base would already violate independence
from B∪D. For reverse transitivity, a parent disjoint from C meeting A
and D cannot meet B, by A↓_C B; it is therefore disjoint from B∪C
and contradicts A↓_(B∪C)D. The same split handles equality intersections.

For stationarity, an unanchored cross pair must have atom n. For a shared
parent meeting C choose c∈C there. E(a,b) holds precisely when E(a,c)
and E(b,c) have the same truth value, including the BOTH FALSE case.
Exactly two sheets makes that case determinate. The cross atom is thus
fixed by the two types over C, and the union-map/homogeneity proof of N08
applies. At C=∅ all cross atoms are n. This gives SIR despite a finite
relative index, without a finite global quotient. Indeed its invariant
equivalences are exactly Id<E<F<Top. An invariant equivalence is a union
of the four pair orbitals. Including d forces e by transitivity through
a point in the opposite sheet; including n forces Top by a point in
another parent. The three proper equivalences all have infinite global
index. This is a direct model calculation, independent of Hasse.

Retain the original AP-only grid warning separately. In I×J with row,
column and neither colours, the missing mixed corner is uniquely
determined over two opposite corners, so SAP fails even though the proper
cover indices are infinite and homomorphic CCO holds. It is NOT a proof
that the grid lacks SIR. Likewise no POCS hypothesis, EPPA theorem or
Ramsey theorem enters any SIR branch here.

## N12: What must return from formalization

The receiving project should return precise compiled statements for the
conditional constructor, its actual source instantiation and the two
boundary branches separately. Report Hasse's provider status explicitly.
Return any mathematical changes through the feedback ledger. Naturality's
onto-base condition, fixed pointwise types and the original-language
two-class premise are highlighted there because they are easy to lose
when an isolated statement is detached from its standing context.
