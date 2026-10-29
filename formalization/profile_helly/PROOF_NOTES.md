# B033 — profile Helly to completion: explicit noncircular proof

Frozen source `490c3f36d85db5a0b3ced0598e6c431825254ec5` is unchanged.
This prepares ONE source result, `lem:helly-to-cco`, not Lean code.
There are NO imported mathematical providers. The abstract table laws,
FULL triangle class and finite positive-profile 2-Helly are the inputs.
Neither the desired CCO nor SAP is an assumption of the proof.

"Total" means that EVERY composable pair of atomic diversity inputs has
a NONEMPTY product, not just that an operation returning empty is defined.
All pair palettes needed by any input/free-amalgam vertex set are nonempty.
The current contract uses the intended fully supported typed setting.
Arbitrary restrictions on which sorts may cooccur are not covered without
an additional availability check. Equality is never a diversity atom.

## N01: Pure table operations and return-square absorption

Extend the atomic product by unions. This immediately gives monotonicity
and union distribution. Reversing a legal triangle gives converse reversal
of products. Associativity is an explicit TABLE premise; it is not proved
by assuming the very SAP which is a conclusion here. Positive profiles
are products of NONEMPTY finite words. They are nonempty: choose one atom
from each successive nonempty factor and use nonempty atomic totality.

Peirce extends to arbitrary typed menus by expanding witnesses:

`(A*B) intersect C != empty`
`iff A intersect (C*bar B) != empty`
`iff B intersect (bar A*C) != empty`.

Every witness is just one allowed atomic triangle, permuted with the
correct typed converses. No actual source, completion or amalgamation
statement is being used. In particular take an atom u:i->j and atom
c:i->k. Choose b in bar(u)*{c}; it exists by totality. Peirce gives
c in {u}*{b}. Since b belongs to the displayed product, associativity yields

`c in {u}*(bar(u)*{c}) = ({u}*bar(u))*{c}`.

This is return-square absorption. It plays the role that logical equality
would play in a RAW calculation, but inserts NO identity atom or zeroth
STRONG profile. It will repair collisions in homomorphic walks.

## N02: Guarded hom-walk readout without SAP or Helly

Let N be any finite complete network all of whose distinct-vertex triangles
are allowed. A positive word walk in N may repeat nonadjacent points.
We prove by strong induction on its length that, whenever its ACTUAL
endpoints are DISTINCT, their actual colour belongs to its table profile.
This is not a claim that the walk is injectively realizable.

Length one is the literal edge label. For greater length let x be the
first point, y the final point and z the penultimate point. If z!=x,
the shorter prefix has distinct endpoints, so induction reads out its
actual x-z colour. Since consecutive diversity edges force z!=y and the
endpoint guard gives x!=y, the three points are distinct. Their allowed
triangle puts the actual x-y colour into the full concatenated profile.

If z=x, the prefix is a positive CLOSED walk. It cannot have length one,
which would be a diversity self-edge. Write its first edge as u:x->w.
The remaining prefix tail w->x has DISTINCT actual endpoints and strictly
smaller positive length than the original walk. Induction reads out bar(u)
in its profile. Thus the closed prefix profile contains {u}*bar(u).
The last edge is the actual x-y colour c. Return-square absorption from
N01 puts c in this prefix profile times {c}, exactly the original word
profile by associativity. This closes the induction, including all
backtracks and repeated earlier terminal visits.

Now suppose a specified simple cycle in G has a HOMOMORPHISM into some
N in K. Cut the cycle at ONE specified edge. Its endpoint images MUST be
distinct, because its label is diversity. The complementary positive walk
can repeat other points, but the proved guarded readout supplies the
converse closing-edge colour in its profile. This gives an algebraic
closing-edge test. Do not cut initially at arbitrary nonadjacent formal
terminals and pretend their images differ: they may have collapsed.
The next note transports the verified test to all other cuts algebraically.

`CycleHom(G)` is only the BOUND per-input condition that every specified
cycle has such a map. It is not an assumption that all G are completable
or that the desired class already has CCO.

## N03: ALG cycle compatibility, rotations and two positive arcs

For a cycle word a0,...,a_last, closing-edge compatibility says
bar(a_last) belongs to Prof(a0,...,a_penultimate), with the indicated
oriented endpoint sorts. For a simple cycle of length at least three,
the middle word B after removing first and last letters remains positive.
Set Peirce and associativity give

`bar(a_last) in {a0}*B iff bar(a0) in B*{a_last}`.

This rotates the closing-edge test. Iterate to obtain all closing edges;
reverse orientations with converse. No zero-word convention is needed.

Equivalently, take two positive arcs P,Q around the cycle, both oriented
from x to y. Their profiles intersect. If P has one letter a, the test
is directly a in Prof(Q). Otherwise P consists of first letter a followed
by positive Ptail. The closing-a test is

`a in Prof(Q)*bar(Prof(Ptail))`.

Peirce is exactly the existence of c in Prof(Q) with
c in {a}*Prof(Ptail)=Prof(P). This proves the common-profile criterion;
reverse the same steps for its converse. It is valid even if a chosen
semantic homomorphism had identified x,y: the initial closing-EDGE test
was obtained at genuinely distinct images, then moved by pure algebra.

Define ALG(G) to mean these equivalent conditions for EVERY specified
simple cycle. ALG is not "this cycle already has a complete extension".
N02 establishes CycleHom(G)=>ALG(G). During the algorithm we maintain
ALG directly, so no intermediate use of the theorem being proved occurs.

## N04: Two paths with arbitrary common-vertex order

For ANY distinct endpoints x,y, RECORDED OR UNRECORDED, enumerate the SIMPLE positive
specified x->y paths in the current finite graph. There are finitely many:
their lengths are at most |V|-1. Their menus are nonempty positive-word
profiles with the same ordered endpoint tags. Repeated profiles cause
no problem. We need no infinite family of arbitrary walks.

The induction below is UNIFORM over all distinct endpoint pairs. The split
subpairs x,v and v,y may already have recorded edges, so restricting the
induction predicate to missing pairs would be invalid. Only after this
uniform theorem is proved do we specialize to the missing xy of a fill step.

Assume ALG(G). Prove any two such path profiles intersect by induction
on the number of shared internal vertices. Identical oriented geometric
paths have the same nonempty profile. Distinct paths with no shared
internal vertex form one specified simple cycle, hence have intersecting
profiles by N03. Two different length-one edges between the same endpoints
cannot occur: a partial network records only ONE colour per unordered pair.

Otherwise choose ANY shared internal vertex v. Both paths split into a
positive x->v prefix and positive v->y suffix. Each prefix pair and each
suffix pair has strictly fewer shared INTERNAL vertices: its common
internals are contained in the old intersection minus v. This remains
true when common vertices appear in opposite orders, or the paths share
edges. There is no hidden compatible-order assumption.

Induction gives p in both prefix profiles and q in both suffix profiles.
Their types compose at v. Choose c in {p}*{q} by nonempty totality.
Monotonicity and associativity put c in both original full profiles.
Nothing here asserts a common actual realization of the two prefix and
suffix choices. It is an algebraic argument in the given table.

Thus ALG makes the finite simple-path family pairwise intersecting. The
assumed 2-Helly property now supplies ONE common c if that family is
nonempty. If there is no specified path, choose any atom from the
nonempty endpoint palette instead. This case does not create an empty
STRONG word or need Helly for an empty family.

## N05: One-edge preservation, termination and derived semantic CCO

Choose an UNRECORDED unordered pair xy and orient it once. Assign the
N04 colour c to xy and its converse to yx, retaining all other labels and
the EXACT SAME formal vertices and sorts. Old simple cycles remain
unchanged. Every NEW simple cycle uses xy once and has a complementary
old SIMPLE x->y path. Its profile contains c by the choice, so N03 gives
ALG for that cycle. If the old path family was empty, such a new cycle
cannot exist. This proves ALG preservation and old-edge preservation.

Importantly, we do not at this step claim a semantic complete realization
of every new cycle. That is unnecessary and would otherwise risk circular
use of the sought completion theorem. The invariant is the proved TABLE
compatibility condition.

The finite number of missing unordered DISTINCT pairs decreases by
exactly one. Induction on that number produces a complete network on the
SAME vertex set, retaining all originally specified labels and ALG. Every
three distinct vertices now form a specified triangle; its algebraic
closing-edge condition is precisely that its table triangle is legal.
Since K is the FULL triangle-defined class, this complete network is in K.
A proper subclass with extra forbidden configurations would not suffice.

We have proved a UNIVERSAL constructor ALG(G)=>fixed-vertex completion,
without assuming CycleHom(G), global CCO or SAP. For the semantic source
statement, N02 first gives ALG from the BOUND CycleHom input, then the
constructor yields a fixed-vertex completion and in particular a
homomorphism. Conversely any homomorphism of G restricts to every specified
cycle. Thus the semantic CCO equivalence is derived. Empty/singleton
inputs have no missing pairs; a missing pair on two vertices is filled
from its palette. None of these cases introduces a diagonal edge.

## N06: Free amalgams, every base visit and the digon case

Take two complete K-networks L,R with embeddings of the same COMPLETE
induced base B. Form abstract copies disjoint outside the whole B and
record exactly their old factor edges. Those colours agree on every
base pair, so the union is a finite partial network. All off-base cross
pairs are unrecorded; the two complete factors are induced and meet
exactly in B. All eventual cross-sort palettes must be nonempty.

A specified cycle contained in one factor is realized in that actual
allowed complete network, hence is ALG by N02. A genuinely mixed simple
cycle must pass between the two off-base sides through B. It cannot have
only one base visit: returning to the other side would repeat that base
vertex. Thus it visits k>=2 distinct base points. Cut at EVERY base visit,
not merely at an informal maximal side segment. Between consecutive visits
is a positive path lying in one factor, with distinct endpoints and no
internal base points. Its actual common-base endpoint colour belongs to
its profile by N02. Length-one base edges are permitted segments.

For k=2, orient the two arcs from the first base point to the second.
Both profiles contain the SAME literal base-edge colour. They intersect,
so N03 gives ALG for the original cycle. Its contraction is a DIGON with
parallel opposite arcs, not a simple two-cycle in B. We never invoke a
simple-cycle assumption at that contracted two-edge object.

For k>=3, the consecutive base vertices and their actual base-edge
colours form a simple cycle inside the complete allowed base, hence ALG.
Choose one closing base edge and consider the opposite positive base
path. Its actual closing colour belongs to the base-path profile.
Each coarse base atom belongs to its expanded factor-segment profile;
monotonicity and associativity therefore put that same closing colour in
the profile of the expanded opposite arc. It also belongs to the reversed
closing-segment profile. These two positive arc profiles intersect. N03
gives ALG for the whole expanded mixed cycle. This is an explicit
substitution calculation, not an assumed realization of the expanded
cycle in a factor or in an already constructed amalgam.

If B is empty the factors are disjoint. If B is a singleton a mixed
simple cycle would repeat it. Thus in both cases all specified cycles
are contained in a factor. We have now verified ALG for EVERY specified
cycle of the free partial amalgam, including these small-base cases.

Apply the GENERIC ALG constructor from N05 directly. It keeps the entire
free-amalgam vertex set and every old colour, so its complete K-network
is a STRONG induced amalgam with intersection exactly B. A mere arbitrary
noninjective homomorphism would not imply this, which is why the fixed
vertex set is part of the constructor contract.

## N07: Forks, compatible sorts and the precise source result

Retain the optional distinct-vertex atomic-fork condition stated in the
source SAP clause. In the intended strong totality/FULL class setting it
has a local witness: for incident a:i->j and b:i->k choose
c in bar(a)*{b}. The corresponding legal table triangle on THREE DISTINCT
formal vertices lies in the FULL K. No assumed ambient SAP is needed to
realize this fork. The source implication under its fork premise therefore
follows from N06, and that premise is locally supplied in this interpretation.

These conclusions require all palettes of pairs appearing in an input or
free amalgam to be permitted and NONEMPTY, including repeated sorts. The
current contract makes full support explicit. If arbitrary incompatible
sorts may not cooccur, two singleton factors over empty base can create
an unavailable cross pair. That setting cannot silently inherit global
SAP or JEP from this proof. Similarly, "total" as merely a Boolean operation
which sometimes returns empty would not provide nonempty path profiles
or the prefix/suffix concatenation witness. Extra forbidden configurations
in a proper subclass would invalidate the terminal FULL-class step.

The single export is `lem:helly-to-cco`, with no additional numbered or
auxiliary equation exports. The apparent semantic collision and intermediate
completion obligations of the short source proof have been explicitly
discharged. The source TeX is unchanged; feedback records these proof/scope
clarifications for a later human pass. Finite table/network controls support
the key invariants and negative examples, but do not certify this all-size
typed theorem. Receiving Lean work must implement these abstract table
contracts; no existing SAP/CCO theorem is silently imported as a premise.
