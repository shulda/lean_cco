# Actual real fibres and the canonical hull

Preparation for other Lean projects; no Lean API or source theorem is
certified here. Five complete source files `real_hull/01` through `05`
contribute eighteen results. The selected upstream result `lem:fibreCCO`
is also expanded and exported; the other finite-group results in its file
are not claimed as covered. Source pins and the DAG are in `module.json`.

## N01: Source and represented support conventions

Use one inhabited transitive ultrahomogeneous complete finite symmetric
binary source. Diversity atom names are disjoint from actual equality 1.
Products are actual represented composition: associative, invariant and
commutative because every original orbital is symmetric. Nonempty invariant
products are nonempty by transitivity. For atoms, 1 belongs to ab iff a=b.
Peirce rotations and atom uniformity include all equality-output cases.

Define H(a,b)=(ab) intersect D for all diversity atoms, so H(a,a)=A_a
where A_a=(aa) minus {1}. H is only a binary guard of RAW multiplication;
it is not a new associative diversity algebra. In all longer calculations
retain the genuine equality atom. No SAP is assumed.

A global equivalence support R means R^+={1} union R is composition-closed.
It defines an original invariant equivalence. Generated supports are least
such supports, obtained by finite closure of the finite palette. The
classes O_R(u)=(R^+u) intersect D partition D. These are support-calculus
classes, not orbits of automorphisms acting on the literal colour names.
An R-fixed colour p satisfies R^+p={p}, which forces p outside R.

The geometric part supplies AP and triangle fullness of the actual age.
The latter is the named `lem:cco-triangle-fullness` provider, available from
AP+semantic CCO. CCO is used directly for fibre/class inheritance. The
separate full Hasse provider is instantiated only on sources whose relevant
homogeneity/CCO hypotheses have been proved.

## N02: Elementary finite triangle Ramsey

Only finite multicolour triangle Ramsey is needed. For k>=1 define
f_k(0)=1, f_k(t+1)=k f_k(t)+1. Starting with f_k(k+1) vertices, repeatedly
choose a pivot and retain a colour class of its outgoing edges to the
remaining vertices. Pigeonhole leaves f_k(t-1) candidates from f_k(t).
After k+1 pivots there is a final vertex. Two pivot colours coincide;
these pivots and the final vertex form a monochromatic triangle.
Thus the least triangle Ramsey number R_k(3) exists. Its exact value is
irrelevant. For k=1 this construction gives three vertices.

An induced finite-palette fibre with no looped diversity colour has size
less than R_k(3), k=max(1,|D|). If it had that many distinct points, finite
Ramsey would give a monochromatic triangle and hence a looped colour.
This replaces the source carrier proof's invocation of infinite Ramsey;
no infinite Ramsey theorem or compactness result is needed.

For Lean, prove the nonexistence of an injection of R_k(3) distinct points
into a class, and deduce finiteness before a natural-number cardinal bound.
A bare Nat.card inequality can be vacuous for an infinite type.

## N03: Relative separator and rectangle/folding

For a finite P of diversity atoms assume intersect_(p in P) A_p subset R.
If u,v are in different support orbits, then u!=v. If every row p failed
to separate them, choose d_p in H(p,u) intersect H(p,v). None is equality:
otherwise p=u=v. Build the triangles with one common actual u-edge, using
AP. Distinct p names force distinct leaves. Triangle fullness constructs
the second apex over the **entire same complete anchor**, with its z-edge
v and the same p-spokes. AP identifies the anchors but cannot identify the
two apexes because u!=v. Their colour lies in every A_p, hence R, a
contradiction. With P empty, its intersection is D and the assertion is
vacuous when R=D; the same convention remains consistent.

Two shared-edge triangle amalgams establish the rectangle criterion for
distinct u,v. Prescribed different colours prevent unwanted apex equality;
SAP is not needed. For folding, take s in R intersect H(u,v) witnessing
u~_R v. An actual triangle and a second triangle along its complete edge
give t' in A_u with t'~_R t. The R/non-R colours force distinctness and
keep t' outside R. When u=v the conclusion is immediate.

## N04: Collapse and square localisation

For R-fixed p and a!=p with A_a intersect A_p subset R, the product ap
is nonempty, equality-free and R-saturated. Two different R-orbits in it
would contradict the separator for the two rows a,p. Thus ap is one orbit.
If c in A_p and A_c intersect A_p subset R, first c!=p (otherwise
p would lie in R); the mixed collapse gives pc={p}. Associativity then
forces A_c subset R.

For an inclusion-minimal blocker family B with intersect A_b subset R,
omitting a fixed row p gives a nonempty outside-R witness set S_i disjoint
from A_p. If x in S_i intersect A_a for a in A_p, actual associativity
produces d in pa with x in pd. Handle d=1, d=p and d in R separately;
each gives a forbidden point of S_i intersect A_p. For the remaining
diversity d, rectangle/separator forces p~_R d, contradicting fixedness.

Now let nonempty P consist of R-fixed colours and T=intersect A_p. If
c in T and A_c intersect T subset R, minimize a blocking family among
A_c and the spoke rows. If c outside R, this blocker must contain A_c.
Two retained spoke rows contradict the preceding square avoidance after
omitting one. The singleton case A_c subset R is immediate; the remaining
two-row case uses self-side collapse. Thus A_c subset R and pc={p} for
every p in P. This is proved **before** finite-fibre globalisation.

## N05: Actual fibres, palette and inherited CCO

Let q(x/A) be a realised type over a finite complete real A with x outside
A. All spokes p_i are diversity colours. Its actual fibre Z is one orbit
of the pointwise anchor stabilizer: adjoin A to a finite partial map and
use homogeneity. The same argument gives homogeneity of the induced fibre.
The realised q is a finite conjunction of literal spoke formulas and
inequalities. Hence this orbit is definable over A: finite orbit is
equivalent to usual real algebraicity over finite A, without an additional
omega-categoricity or Ryll-Nardzewski provider.

Its diversity palette is exactly T=intersect_i A_(p_i). One inclusion is
the anchor/new/new triangle condition. For the converse, adjoin two
distinct new points of q to the **same complete anchor**, with any chosen
d in T between them. Triangle fullness and anchor alignment realise the
diagram over actual A. The same construction for arbitrary complete legal
fibre diagrams proves inherited triangle fullness. Empty anchor is allowed;
the palette is then all D. Singleton fibres have empty diversity palette.

For fibre CCO, adjoin one shared complete anchor and all fixed spokes to a
partial fibre diagram. A mixed simple cycle splits into independent fibre
path segments between visits to anchors. Each actual fibre edge colour is
serial at every fibre point by stabilizer transitivity, so each segment has
an endpoint-free walk in Z. A zero-edge segment uses any realised q-point.
The source cycle's distinct segments share no non-anchor formal vertex.
Their maps and the prescribed anchor visits therefore combine into a
homomorphism. Original CCO gives a map of the whole anchored diagram; its
complete anchor is injective, and homogeneity aligns it pointwise to A.
All new images then lie in Z. Neither globalisation nor arbitrary imaginary
CCO nor injectivity of unspecified new vertices is used here.

## N06: Fibre-closed supports and the canonical spoke fixer

Call R **fibre-closed for Z** when it is a global invariant equivalence
support and every R-class meeting Z lies wholly in Z. This translates the
source's phrase "exact for Z". It does not assert RAW word-exactness.
Spoke fixedness follows by anchoring a witness of a raw product r p_i at
the actual p_i-pair. A putative equality output puts a parameter a_i in Z,
contradicting x outside A; every other output must again be p_i.

For nonempty spoke set P define R_P={d:p d={p} for all p in P}. Actual
associativity and nonempty products show that every diversity output of
d e for d,e in R_P lies in R_P; equality outputs stay as the true unit.
Thus R_P is a global equivalence support, and is largest among supports
fixing every p. Its classes meeting Z stay in Z, since every point retains
all literal spokes and cannot coincide with an anchor. Every R_P colour
occurs from any chosen z in Z by original transitivity, so R_P subset T.
This construction precedes any finiteness or internal Hasse argument.

## N07: One internal cover globalises the finite fibre

For a finite actual Z, inherited homogeneity/transitivity/CCO permit use of
the prepared full Hasse theorem on this source Z. Every internal cover has
relative index two. A saturated internal chain also gives |Z|=2^m with
m no larger than its number of actual diversity orbitals, hence <=|D|.
This finite-size statement needs no globalisation or word-exactness.

If R_P is properly below T, choose just **one** full internal cover above
R_P restricted to Z. For each colour c in its difference layer, two
internal c-edges return to the lower equivalence. For d in A_c intersect T,
adjoin three distinct new q-points over the same complete anchor with
triangle (c,c,d). Triangle fullness realises them in Z, transferring the
internal square statement to the original statement A_c intersect T subset
R_P. N04 localisation then gives pc={p} for every spoke, so c in R_P,
contradiction. Hence R_P=T and Z is one original E_T-class.

This proves existence without globalising any intermediate internal
equivalence. If Z is a singleton, T=R_P is empty and E_T is true equality.
For empty A, the fibre is M by transitivity; it is finite precisely when
M is finite, and its support is the universal diversity support D.

## N08: Generic invariant classes and the correct uniqueness interval

For an arbitrary original invariant equivalence E and one class C, all old
colours below E occur in C by moving the first endpoint of a realised
edge into C. The induced class is transitive and homogeneous: a nonempty
partial map extends ambiently and its image point forces C to stay fixed;
the empty map uses the identity. This elementary part uses no CCO.

Each restricted old atom is one orbital of the **full** Aut(C). Therefore
every internal invariant equivalence is a union of literal old colour
names. Extend that union to all of M. To prove transitivity, move a whole
relevant E-class into C using one ambient automorphism and use transitivity
of the internal equivalence there. Restriction and extension give
[Id,E] ~= InvEq(C). This does not require every automorphism of C to
extend to M, nor any distributivity of the full invariant lattice.

After N07 establishes Z as one E_T-class, this generic interval theorem
globalises every internal chain, with indices preserved. **Uniqueness is
within [Id,E_T], equivalently among fibre-closed lifts.** Unrestricted
global uniqueness is false: for proper E_T and internal Top_Z, both E_T
and Top_M restrict to Top_Z. The source's nearby interval assertion gives
the intended scope of its proof wording. Prove the generic interval once
independently, then apply it after existence; never use it to supply the
missing existence of E_T. The source also gives a direct extension proof.

The fibre palette and R_P depend only on the set of spoke names. For any
realised type with this same nonempty P, it is one R_P-class iff T=R_P.
Consequently finiteness is equivalent to T=R_P plus finite R_P-class size.
If one such type is finite, all such fibres are whole classes of the same
invariant equivalence, with equal two-power size and ambient conjugacy.
No automorphism transporting their parameter configurations is claimed.

## N09: Class CCO and finite-class indices

The triangle-fullness part of class inheritance uses a complete R-coloured
diagram, original triangle fullness, and one automorphism moving the
realised class into C. For CCO, complete each specified-edge component
in M and move its image E-class into C independently. Maps may overlap;
there are no specified edges between different components.

For a finite-class original E, a cover H<K<=E in [Id,E] is already a
cover in the full original lattice: any intermediate equivalence remains
below K<=E. Its relative index is finite, so the prepared **original full
Hasse theorem** directly gives index two. Alternatively use inherited class
CCO plus N08. A saturated interval chain yields |E-class|=2^m; each strict
step adds an old diversity atom, so m<=|R|. This does not make the full
interval distributive: I times F2² gives a genuine CCO M3 packet interval.
It also does not make every finite-class original equivalence RAW exact.

## N10: Relative pseudocomplement

For nonempty R-fixed P, S=intersect A_p and
W_R(P)={a:A_a intersect S subset R}. First R subset W. Fixedness gives
R^+(pp)=pp, including equality, hence R^+ subset pp. Removing R^+ shows
each A_p minus R, and therefore S minus R, is saturated under the colour
support orbits. Equality outputs must be removed at this point explicitly.

For a in W outside R and x in A_a, a hypothetical t in A_x intersect
S minus R yields d in ax with t in ad. Handle d=1 and d=a first. For the
remaining diversity d, separator applied to {a} union P forces a~_R d;
folding and saturation put an outside-R point in A_a intersect S, a
contradiction. For a in R square closure is immediate.

For distinct a,b in W and c in ab, a hypothetical t in A_c intersect
S minus R similarly gives d in bt with c in ad. Handle d=1 and d=b.
Rectangle identifies failure of the a-row to separate b,d; the spoke rows
also fail. Separator, folding and S-minus-R saturation yield the same
contradiction. Thus W^+ is composition-closed. No RAW exact calculus is used.

## N11: Carrier insertion and looped diagonal Helly

For a realised finite star with nonempty P and extra spoke b set
S=intersect A_p, C=S intersect A_b. If b is already in P the conclusion
is immediate. Otherwise adjoin the complete actual anchor; N05 identifies
its fibre palette exactly with C. If C has no looped colour, N02 makes
this realised fibre finite, including the singleton case C empty.
N07 globalisation makes C a global support fibre-closed for Z. Spoke
fixedness makes all p in P C-fixed, so W_C(P) is a global support. Since
A_b intersect S=C, it contains b and hence the generated support of A_b.
A looped r in S intersect <A_b> outside C would then satisfy both r in W
and r in A_r intersect S minus C, contradiction. This proves insertion.

For looped diagonal Helly process finitely many rows, maintaining a looped
r satisfying processed A_p and all remaining generated supports <A_p>.
If r is the next row, keep it. Otherwise apply carrier insertion with the
processed rows **and the extra current row r**, keeping this family nonempty.
The new looped r' lies in A_r, so every generated equivalence containing r
contains r'. This preserves the invariant. With zero rows the assertion is
the tautology L nonempty => L nonempty. No support Helly import is used.

## N12: Even walks and the canonical class bound

Gamma(p)=<{p}> is connectivity of the old p-graph, while B(p)=<A_p>
is even connectivity. Seriality gives Id subset p²; finite orbital supports
and two-step backtracks represent B(p)^+ by a stable **positive even**
word. Ordinary positive powers need not stabilize without tracking parity.
Gamma(p)^+ need not be RAW exact: for a thin F2² translation atom it is
Id union p, whereas every word profile is an individual difference atom.
Connectivity has one or two even classes. A looped colour cannot lie in
the odd sheet, since its triangle could not cross a two-class bipartition.

If x is algebraic over finite A and outside A, its actual fibre is finite.
No colour of its palette T is looped: such a colour would permit arbitrary
finite cliques of new q-points over the same anchor, by triangle fullness
and homogeneity, contradicting finiteness. This argument also applies to
the empty-anchor finite source. It needs no Ramsey or globalisation.

Put J=intersect Gamma(p_i). If any E_J-class had at least R_k(3) points,
finite Ramsey would produce a looped r in J. Even-walk geometry puts r
in every <A_(p_i)>, and N11 looped Helly supplies a looped colour in T,
contradiction. Every E_J-class is therefore uniformly small. The displayed
canonical hull is precisely [x]_(E_J), because each x and a_i already
share their generated class. It contains the anchor-stabilizer orbit but
need not equal that orbit or the one-point fibre: in the two-sheet example
a two-point fibre has a four-point canonical hull.

For empty A the canonical class is M; transitivity makes algebraicity
equivalent to M finite. For x in A use equality and a singleton hull;
do not apply diversity Gamma notation to col(x,x). Once the canonical class
is finite, N09 gives its two-power size <=2^|J|<=2^|D|. This use of finite
Hasse sizes does not replace the preceding proof of canonical finiteness.
The reverse criterion, finite canonical class => x algebraic, follows from
orbit containment; the larger bounded-character/palette-cost development in
`real_hull/06` and the SAP results in `07` are separate future packages.
