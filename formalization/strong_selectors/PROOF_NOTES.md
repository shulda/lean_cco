# STRONG calculus, PC and hereditary selectors: additional proof details

This module covers three existing files: `typed_strong_domains.tex`,
`typed_pc_fixedpoint.tex` and `typed_hereditary_selectors.tex`. It prepares
their 15 result exports for formalization without changing the human TeX.
The exact contracts and dependencies are in `module.json`.

## N01: Three different sets of hypotheses

The base source U is an actual homogeneous complete binary relational
structure, with finitely many nonempty named transitive sorts, finite
diversity palettes, symmetric same-sort atoms and correctly typed converses.
Its actual finite age has SAP. Logical equality is separate from every
diversity palette. Distinct formal vertices must remain distinct in a
strong completion, including when their sort labels agree.

Semantic homomorphic CCO is an additional premise: every finite specified
typed diversity diagram whose specified simple cycles have homomorphisms
has a homomorphism itself. NR2 is a third premise, used only in the
loop-stabilization/no-return route: the FULL lattice of original invariant
equivalences on each named sort has no proper interval of relative index
two. It is not enough to inspect only the exact sublattice, or only
globally finite quotients. Primitivity is not needed.

The RAW module is not a theorem prerequisite for these proofs. They share
elementary represented-relation and word notions, but RAW exact-ball Helly
is not silently imported as STRONG Helly. The strengthened injectivity is
supplied by SAP of this actual source.

## N02: SAP, infinite stabilizer orbits and collision removal

For a finite complete B⊆U and v∉B, strong amalgamate n copies of B∪{v}
over B. The n new points are distinct and have the same finite type over
B. This finite amalgam belongs to Age(U), so it embeds into U. Homogeneity
aligns its copy of B with the prescribed B, and maps its n new points
into the orbit of v under Aut(U/B). The orbit has at least n points for
every n, and is infinite. This argument uses neither CCO nor a coset-cover
theorem.

Given a homomorphism of a finite partial diversity diagram, pin any set S
on which it is already injective. Process the other formal vertices in
any finite order. For the current vertex x, take B to be the set of
current images of its specified neighbours. Its current image is outside
B because every specified edge is irreflexive. Move that image within its
infinite orbit over B to avoid the entire current finite image and the
finite forbidden set. Change only x. Every specified incident edge keeps
its colour, while all other edges are unchanged. Later moves avoid the
images already fixed, so they cannot recreate a collision. At the end all
formal vertices are distinct, S remains fixed, and the unpinned images
avoid the forbidden set. Neighbours are a set of images, not an assumed
injective list of formal vertices.

## N03: Strong product, paths, Set-Pasch and duplication

For A⊆L_ij and B⊆L_jk, define A*B using actual legal triangles on
three distinct real points. Use arbitrary subsets, including empty, for
temporary Boolean algebra; exact menus themselves are nonempty. Products
are monotone, respect unions and typed converse, and Peirce rotation is
obtained by permuting an actual triangle. SAP amalgamation of two edges
over their common point makes compatible nonempty products nonempty.

For associativity, an output of (A*B)*C comes from a triangle on vertices
0,2,3, and a second triangle on 0,1,2 with the same complete 0–2 edge.
SAP amalgamates them over that edge with all four points distinct. Its
1–3 edge witnesses the other parenthesization. Reverse this construction
for the reverse inclusion. A subset of a loop palette is self-converse;
hence loop products commute. This does not permit reordering cross-sort
arrows.

Typed Top absorbs every compatible nonempty menu: amalgamate a chosen
output edge and an edge in the nonempty menu over their common endpoint.
The remaining edge belongs to Top. For Set-Pasch, two triangles realizing
the same output atom amalgamate over that complete edge. Their off-base
vertices remain distinct, and their connecting atom is in both rotated
products. No CCO, NR2 or exactness is involved.

For an atom c:i→k and any menu X:i→j, the duplication law is
X⊆{c}*{c̄}*X. For each x∈X amalgamate a c-edge and an x-edge over
their i-vertex, using SAP so the other two endpoints are distinct. The
resulting triangle gives b∈{c̄}*{x} and x∈{c}*{b}. This is also valid
when some or all of i,j,k coincide. Applying it to a nonempty loop P
gives P⊆P³, by choosing c∈P and using self-converse loop atoms.

Iterated strong products equal the endpoint colours of injective positive
word paths. Prove this by gluing the last triangle to a path along its
complete endpoint edge, using SAP. Conversely read an injective path one
triangle at a time. A represented word walk with distinct endpoints can
be injectivized by N02 with those two endpoints pinned. Thus its guarded
represented profile equals its strong profile. Delete identity letters
before applying this statement; an all-identity word has no diversity
survivor. There is no empty-word strong identity element.

## N04: Strong CCO, theta Helly and prescribed atoms

CCO first supplies a homomorphism of a specified diversity diagram. N02
then makes it injective. For a prescribed complete base, its homomorphic
image is already an induced copy, since every distinct pair has one
specified diversity atom. Align this image by homogeneity, then pin it
during injectivization. This proves the strong cycle criterion.

For strong word Helly, connect two formal roots by reduced positive
private paths. Merge duplicate length-one branches: all direct singleton
profiles agree whenever the family intersects pairwise. Each remaining
simple cycle consists of two private paths. A shared output atom realizes
both paths with the same distinct root pair; SAP glues their interiors.
CCO completes the theta homomorphically. Pin only ONE root when applying
N02, since the CCO map might identify the two roots. The resulting distinct
roots have an atom in every profile. The empty list is the bare-root Top
case. Flattening presentations gives exact-menu Helly and closure under
meets whose RESULT is nonempty.

For exact endpoint semantics, prescribe an atom d in the menu and add its
direct root edge. If a direct edge already exists, it has the same colour
and is merged. All new cycles use compatible private paths. The resulting
strong completion realizes d, proving that the menu is the full survivor
set rather than merely an upper bound. If Top was explicitly adjoined as
a profile without a word presentation, discard that restriction first;
it contributes no private branch.

## N05: Exact products and three-root occurrence

The exact convolution proof uses strong Peirce and word Helly twice. For
nonempty A=⋂r P_r and B=⋂s Q_s and an atom z in every P_r*Q_s, the
profiles P_r and {z}*Q̄_s intersect pairwise: A witnesses the first
group, any b∈B gives the common nonempty subprofile {z}*{b̄} for the
second, and Peirce gives every cross intersection. Helly yields a∈A
in all those rotated profiles. Apply Helly again to the Q_s and
{ā}*{z} to obtain b∈B with z∈a*b. Concatenation supplies the product
presentation. Top absorption handles an empty defining list. Flattening
presentations proves distribution by a nonempty exact factor over a
finite exact meet whose evaluated intersection is nonempty. No such law
is asserted for arbitrary invariant or arbitrary nonexact menus.

PC(A,B,C) means ALL THREE support inclusions:
C⊆A*B, A⊆C*B̄, B⊆Ā*C. It is stronger than the existence of a legal
triangle in the product of menus. Rotations retain their actual types.
The same menu variable can occur in several coordinates; the three formal
root vertices remain distinct.

For three-root occurrence, put a private theta on each side of a root
triangle. Every simple specified cycle either stays on one side (two
branches) or uses one branch on every side. PC supplies a legal atom
triple in the three exact menus, so the second kind is realizable by
gluing private paths to that actual triangle with SAP. Apply CCO and
injectivization. To realize any prescribed atom on one side, use the
corresponding PC inclusion to choose the other two atoms, and add the
three root edges. Merge any equal direct branch; PC ensures its prescribed
colour agrees. This also handles a Top side with no branches: the added
root edges supply the needed triangle directly. Exactness of the gadgets
then gives precisely the requested three endpoint domains.

## N06: Finite PC iteration and the simple-path formula

Maintain domains on ordered pairs of DISTINCT formal vertices only, with
typed converse. Initialize specified edges to their singleton and other
pairs to the diversity Top. A synchronous update intersects each current
domain with all two-step products through third vertices distinct from
both endpoints. Empty domains are allowed while running the algorithm.
The product on Boolean subsets is monotone, so the update is monotone and
deflationary. The finite total number of surviving atoms decreases until
a fixed point is reached. Any stable refinement of the initial network
is included in every iterate, by induction, and hence in the limit. This
is the precise greatestness property used below.

Any actual injective completion survives every update: its triangle on
three distinct vertices supplies the two-step support at each stage.
Thus a strongly completable graph has no empty fixed domain. In a nonempty
fixed network, the triangle inclusions propagate along every specified
simple path by induction on its length and product associativity. Its
fixed endpoint domain is therefore included in the path's profile.

Let A(x,y) be the intersection of all specified simple x–y path profiles,
with empty family Top. Suppose all fixed domains are nonempty. For an
old specified cycle remove one edge xy=t. The fixed domain on that edge
is {t}, and propagation along the remaining path puts t in its profile.
Consequently the old cycle is realizable. For any c∈A(x,y), add xy=c
(or retain the equal already specified edge). New simple cycles consist
of this edge plus one old simple x–y path, so all cycles are realizable.
The strong cycle criterion gives an injective completion of the augmented
graph. Its colours on xz and zy lie in A(x,z), A(z,y), and support c.
Thus A is itself a stable refinement of the initial network. Greatestness
gives A⊆D∞; propagation gave D∞⊆A, proving the walk formula.

This argument proves more than mere local consistency: every surviving
atom extends to a completion of the whole graph. It still requires the
source CCO and SAP assumptions. A general constraint network with PC
need not have this property.

## N07: Canonical PC domains and simultaneous triples

The walk formula expresses any fixed domain of a completable graph as a
finite intersection of positive profiles. Conversely a private theta for
any exact menu is strongly completable by N04 and has exactly its defining
root paths, giving that menu as its PC fixed domain. Top uses two bare
roots. Therefore canonical nonempty PC domains equal the original exact
family, rather than a new family with an invented product.

For the three-theta graph, a simple path between two roots either uses
one branch of their own theta, or one branch on each other side. It cannot
revisit a root. The walk formula and exact product distribution therefore
give A∩(C*B̄)=A, and its rotations, under the PC inclusions. If a side
is Top, its list is empty and the corresponding product of restrictions
is Top by absorption; no path through a missing branch is invented.
This proves the simultaneous three-PC-domain assertion.

## N08: Current families, visible filters and gates

All families are tagged by ordered endpoint sorts and are subfamilies of
the ORIGINAL exact system H. A current family J contains all atomic
singletons, is converse closed and is downward closed among nonempty
original exact submenus. A generated filter F is converse closed and
closed under multiplication on either side by every compatible original
exact menu. Products never change after a gate.

Visibility says that two parallel F-menus meeting one current D must
intersect each other. Active filters together with D are therefore a
pairwise-intersecting finite family. Exact Helly makes their intersection
G(D) nonempty exact; downward closure keeps it in J. An empty active list
leaves D unchanged. Converse carries active lists bijectively.

If E⊆D is current and E meets G(D), every filter active on D meets E;
the reverse implication follows from E⊆D. Thus their active lists agree,
and G(E)=E∩G(D). Survivor heredity is proved here rather than inferred
from conservativity or triangle legality.

## N09: Bilateral support and all three PC coordinates

Suppose D⊆P*E and E⊆P̄*D, with D,E current and P any original exact
menu. For each filter A active on E, choose e∈A∩E. The reverse support
inclusion gives d∈D supported through P with e. Hence P*A is a filter
active on D. The gate is contained in P*E and in all P*A. Distributing
over the nonempty evaluated intersection defining G(E) gives
G(D)⊆P*G(E). Exchange the two sides for the reverse inclusion; converse
gives the right-factor version. P need not belong to the current family.

For PC(A,B,C), fix c∈G(C). Applying these fixed-factor implications to
the original PC triple gives c∈A*G(B) and c∈G(A)*B. Define the original
exact restrictions A_c=A∩({c}*B̄), B_c=B∩(Ā*{c}). They meet their
respective gates by those two witnesses, so are nonempty current menus.
Heredity identifies G(A_c)=A_c∩G(A), G(B_c)=B_c∩G(B).

Exact distribution and duplication from N03 give both inclusions
A_c⊆{c}*B̄_c and B̄_c⊆{c̄}*A_c. For example,
{c}*B̄_c=({c}*B̄)∩({c}*{c̄}*A) contains A_c. Apply bilateral support
to (A_c,B̄_c), with fixed factor {c}. A point in the nonempty G(A_c)
then supplies b∈G(B_c) and c∈a*b. Thus G(C)⊆G(A)*G(B). Run this
argument on both correctly typed PC rotations for the other two
inclusions. An arbitrary supported triangle alone would not prove this
for every c, or prove the rotated coordinates.

## N10: Gate images, composition and finite descent

For every original nonempty exact E⊆G(D), heredity gives G(E)=E. Thus
G fixes its own image and that image equals its fixed family, is
downward and converse closed, and contains all atomic singletons.
An active proper trace A∩D⊊D forces G(D)⊊D; the old D cannot be fixed
or in the image. The finite number of current tagged menus decreases.

For successive gates, if E⊆D meets G₂(G₁(D)), it also meets G₁(D).
Heredity of G₁ gives G₁(E)=E∩G₁(D), which meets G₂(G₁(D)). Apply
heredity of G₂ to this inclusion, obtaining the composite heredity
formula. Nonemptiness, conservativity, converse and PC preservation
compose as well. This permits every intermediate image to remain in
the original exact system.

## N11: Even/odd powers and the exact use of NR2

For a nonempty loop menu P and positive n≥1, duplication gives
Pⁿ⊆Pⁿ⁺². No zeroth strong menu power is used. The even and
odd chains stabilize separately in the finite palette. Their eventual
values J,O satisfy J*J=J, J*O=O, O*O=J, and P⊆O. Take all power
indices large enough when deriving these identities by associativity.

For t∈J, J*{t}=J. One inclusion is idempotence; for r∈J choose
u∈r*t by SAP, so u∈J and Peirce gives r∈u*t. If t is also in O,
J=J*t⊆J*O=O; then O=J*O⊆O*O=J, so J=O.

Otherwise J,O are nonempty disjoint invariant diversity relations.
On the actual original sort let R=Id∪J and S=Id∪J∪O. They are
reflexive and symmetric. The multiplication identities imply transitivity
on distinct points; equality cases are automatic. For each point x,
its O-neighbours are nonempty by orbital transitivity. Two distinct
O-neighbours are J-related by O*O=J. Every point R-equivalent to an
O-neighbour is again an O-neighbour of x, by O*J=O and equality cases.
Hence S[x] consists of exactly two R-classes, R[x] and the O-class.
They are distinct because J∩O is empty. This produces the forbidden
FULL invariant relative-index-two interval. NR2 therefore forces J=O
and all sufficiently high consecutive powers to agree. Their stable
value need not be the full loop palette. CCO is unused in this argument.

## N12: Generated normal forms and parallel no-return

Every menu generated from C by original multiplication and converse has
form P*C*Q or P*C̄*Q, with either outside multiplier possibly absent.
An absent multiplier is the identity ACTION on menus; it is not a new
strong menu or logical equality atom. Prove the forms inductively under
each generation rule, reversing order and taking converses when needed.

For a generated return with C:i→j, a same-orientation expression has
loop or absent multipliers at i and j. If i=j, self-converse loops also
handle the opposite orientation. If i≠j, a reverse expression P*C̄*Q
returning to (i,j) has P,Q:i→j, both present. The loop P*C̄ is
self-converse, so P*C̄=C*P̄. The expression becomes C*(P̄*Q), with a
right LOOP multiplier. There is no product C*C of two cross arrows.

If parallel A,B generate the same family, returns T(A)=B and V(B)=A
have loop/absent multipliers. The two transformations commute, since
loop multipliers commute on each endpoint sort. Loop stabilization makes
Tⁿ=Tⁿ⁺¹ for large n, including the identity action when a multiplier
is absent. From VT(A)=A obtain VⁿTⁿ(A)=A. Then
B=T(A)=T VⁿTⁿ(A)=VⁿTⁿ⁺¹(A)=A. This proves no-return without
assuming the current contracted image has a new associative algebra.

## N13: Conditional pure-tag engine and the final selector

A pure tag action permutes named sorts while fixing literal fine-colour
names and transporting triangle legality, converse and products. For its
conditional engine, assume the displayed generated-family no-return
property for every seed. This property is an actual premise of the
general engine, not a consequence of an arbitrary tag or colour action.

If a current menu D is nonsingleton, an atomic singleton in D has a
nonempty proper current trace. Among all viable ORIGINAL exact seeds
choose one whose action/converse/product-closed generated family has
least cardinality. If visibility failed at D', two disjoint generated
parallel A,B meeting D' would themselves have nonempty proper traces.
Their generated families are contained in the chosen family. If both
were equal to it, assumed no-return would give A=B, contradicting their
disjointness. One inclusion is strict, contradicting minimality. Thus
the selected family is visible and its gate is valid.

Start with the action-invariant current family J₀=H. At every step the
entire generated family is action invariant, even if the chosen seed is
not. Because the current domain is also action invariant, active lists
are transported bijectively, so the gate commutes with the pure tag
action and its image is again an action-invariant current family.
Each proper gate strictly reduces
the number of tagged current menus while keeping every atomic singleton.
There are at most Σij|H_ij|−Σij|L_ij| such steps. At termination every
image menu is a singleton; the composite gate gives one conservative,
converse-compatible, PC-preserving hereditary selector.

For the unconditional named-sort HS theorem use the TRIVIAL tag group.
Its generated no-return premise is supplied by N12 under source NR2.
No nontrivial pure-action premise remains in that theorem. It asserts
no covariance under permutations of actual fine-colour names, and does
not give safe all-row readings automatically. Those EPPA interfaces
require the separate augmented safe construction.

## N14: Scope of this preparation and article feedback

The module stops at joint HS. The SIR free-span network, selected amalgam
and transitivity arguments are later consumers, not imports. Terminal
pure powers and safe EPPA readings are also separate modules. No new
proof-assistant declarations or provider imports have been compiled.

Two independent model review passes and parent synthesis found no required
mathematical theorem repair in this bounded source. Formal detail added
here includes explicit finite PC greatestness, completion-survivor
induction, gate composition domains, stabilized power thresholds and the
two-class argument on actual invariant equivalences. Optional wording
clarifications for a later human pass are recorded in `article_feedback`.
