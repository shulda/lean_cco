# B038 — relational clones and complete-input triangle fullness

Frozen source `490c3f36d85db5a0b3ced0598e6c431825254ec5`.
Two independent Foundations I results are prepared in ten definitions,
35 claims and six tasks, with no imports or external theorem nodes:

- `sections/foundational_sap_collision_unfolding.tex`,
  `lem:collision-unfolding`;
- `sections/triangle_fullness.tex`, `lem:cco-triangle-fullness`.

The collision signature need not be finite; all symbols are relational
of finite arity, with no functions. Triangle fullness instead concerns
the COMPLETE atomic binary code. That branch uses ordinary AP plus
semantic homomorphic CCO, without the collision helper or an assumed
FULL triangle class. Source TeX remains unchanged.

The accompanying [provider-cache plan](../EXTERNAL_PROVIDER_BUILD_CACHE.md)
is receiving engineering guidance, not a mathematical premise or a public
CI configuration change. The five existing HN/HKN binding records remain
unchanged.

## N01: Tuple supports and separate target-image invariants

**D01–D04; C01–C03.** In a pure relational structure, the induced support
on all DISTINCT entries of a displayed positive tuple is irreducible.
A free split has to place that WHOLE tuple in one factor, which then
contains the entire support, contradicting properness. This works for
every finite arity, including tuples with repeated coordinates. Nullary
truth is unaffected by a change of vertex images.

Since h is a HE, it is injective on every irreducible source piece. Such
a piece therefore contains at most one distinct point in any collision
fibre F_v. This applies in particular to every positive tuple support,
which will establish GLOBAL homomorphism preservation, not just the
protected-piece part of the HE condition.

Each distinguished complete source factor S_i also contains at most one
point of F_v, by its separately assumed h-injectivity. The invariant is
injectivity on S_i and the FULL induced type of its TARGET IMAGE h(S_i).
This does not assume h reflects the source factor and does not preserve
the joint type of several such images or all their literal positions.
Even where source completeness is not needed by this proof step, retain
it from the source theorem.

## N02: A full induced clone fixed over every other old image

**D05; C04–C08.** Let B be the full finite induced structure of U on h(A).
It includes all target relations, not merely the displayed partial source
diagram. Because there are NO functions, B minus {v} is an actual induced
age substructure. Unary sort predicates and nullary truth are retained.

Strongly amalgamate TWO copies of B over that entire base. Their images
intersect exactly in the base, so their two copies of v differ and lie
outside it. The age host may have additional points; no union-of-factors
requirement is used. Embed this finite age object into U.

Its first B-copy is induced-isomorphic to the literal old B. Homogeneity
extends that inverse identification to an automorphism of U. Apply it to
the WHOLE amalgam, aligning the first copy pointwise onto B. The second
copy of v is then vprime OUTSIDE ALL of old B, while the shared base is
literally unchanged.

The second copy supplies an induced map g_v:B->Bprime, identity outside
v and sending v to vprime. It preserves and reflects the full relational
diagram of B: all arities, repeated-coordinate instances, negative
information, unary tags and nullary truth. The finite vertex sets need
not have only finitely many relation symbols. No enumeration of the
signature or choice of representative colours is used.

## N03: Split fibres, retain global HE and descend a finite measure

**D06; C09–C16.** Choose a nonempty proper T subset F_v and send precisely
its source vertices to vprime. Keep the other fibre vertices at v and
all other images unchanged.

For every displayed positive tuple, N01 gives at most ONE distinct
F_v point in its support. All repeated occurrences of that source point
move together. Its target tuple is unchanged or obtained through the
full induced clone map g_v. Thus EVERY positive relation is preserved;
this explicitly proves global homomorphism preservation at arbitrary
arity. Nullary truth was unchanged throughout.

Every irreducible source piece likewise sees at most one F_v point. Its
new restriction is either the old embedding or g_v composed with it.
It remains induced, so the whole new map is a HE. The distinguished
factors obey the same one-point condition by their assumed injectivity:
each target image is unchanged or induced-isomorphic to its previous
image via g_v. Their injectivity also survives because vprime was not in
ANY old image.

For a fibre of size r split into sizes t and r-t, the collision-pair count
decreases by exactly

\[
 \binom r2-\binom t2-\binom{r-t}2=t(r-t)>0.
\]

Other fibres are unchanged and cannot collide with the fresh value.
Equivalently image cardinality increases exactly one. Iterate while
there is a collision. The HE and distinguished injectivity hypotheses
persist, so every next step is legal; the natural measure terminates.
At zero it is injective, and composing the per-step image isomorphisms
retains each ORIGINAL distinguished image type.

Already injective maps, empty sources and singleton sources can be left
alone. Countability is retained from the theorem, though the finite proof
uses only age embeddability and homogeneity. The result is an INJECTIVE
HE, not necessarily a globally induced embedding of the partial source.
There is no CCO or binary-language premise in this branch.

## N04: Ordinary AP builds homomorphic partial star fans

**D07–D10; C17–C23.** Fix any specified simple m-cycle of COMPLETE A,
with vertices v0,...,v(m-1), m>=3. The source hypothesis puts every
actual triangle {v0,vi,v(i+1)} and every complete shared edge in K.
Their actual A chord colours are used; no new colours are chosen.

The fan F_i records ONLY the star edges from v0 to vertices already
introduced and the consecutive path edges, with their converses and
typed atomic data. It is not the full induced A on that vertex set.
Begin with the first actual triangle and its identity realization in K.
Maintain a colour homomorphism F_i->H_i into a complete K host.
For incoming T_i={v0,vi,v(i+1)}, i>=2, the CURRENT fan is F_(i-1)
and its host is H_(i-1); the extension constructs F_i.

The restriction of that map to the shared complete edge v0-vi is an
induced embedding. Its irreflexive diversity atom forces its two images
distinct; source and target have the same unique atom, converse and
complete unary tags, which give reflection on the edge. Thus it is a
legal AP span between current H_(i-1) and incoming actual triangle T_i.

Apply ordinary AP to get a new K host and induced maps of both factors.
Compose the ENTIRE old fan map with the old-host embedding. Send the
incoming formal vertex through the new triangle map. Agreement on the
shared edge makes the combined map well-defined. It preserves every old
recorded edge, adds the next path edge and the next star chord, and
retains all converse/sort data.

The incoming vertex can coincide with some earlier NONADJACENT formal
vertex image. AP need not be strong, and the invariant has deliberately
not recorded the other A chords that might prohibit such a coincidence.
It cannot coincide with either endpoint of its triangle, whose complete
edge colours are irreflexive.

After triangles i=2,...,m-2, final F_(m-2) contains the first edge, every
consecutive cycle edge and the closing star edge to v0. Restrict its
homomorphism to the specified cycle. This works for EVERY cycle, with
possibly different finite hosts and collisions. Up to this point the
argument uses AP and genuine small A diagrams, not semantic CCO, SAP or
the desired triangle-fullness conclusion.

## N05: CCO and COMPLETE atomic input yield an induced embedding

**C24–C29.** Every small type/pair of A is allowed and every specified
cycle has its N04 homomorphism. Apply semantic HOMOMORPHIC CCO to obtain
ONE homomorphism of the entire complete A into some H in K.

For any distinct x,y, A has a specified irreflexive diversity atom on
that pair. Preservation in H prevents h(x)=h(y), so this whole map is
injective. There is no SAP or separate collision-unfolding step here.

To reflect a target atom b on h(x),h(y), take A's unique atom a on x,y.
It is preserved; the complete target's exclusivity forces b=a. Thus
all binary atoms reflect. Complete exclusive unary tags are preserved
and reflected; converses, logical equality and false diversity diagonals
agree as well. Arbitrary extra predicates outside the complete atomic
code are not part of the theorem. The map is an induced embedding.

Its actual induced image belongs to K by heredity, and isomorphism
closure gives A in K. If |A|<=3 this is already a direct instance of
the premise, including empty/singleton/edge cases. Triangle fullness has
been DERIVED, without assuming that K was the full triangle-defined class.

Existing earlier modules mention this triangle law as human support.
This standalone proof provides a source-linked provider for later review;
their existing contracts are not silently rewired by this private batch.
In particular B033's FULL-class premise must not be imported here to
prove the fullness conclusion itself.

## N06: Boundaries and actual finite controls

**C30–C35.** Bounded controls examine actual maps, tuples, clone diagrams
and fan witnesses. The mathematical boundary arguments also have the
following direct forms; finite enumeration is not an unbounded theorem.

- AP alone does not unfold collisions. A countable homogeneous matching
  graph has an AP age, but not SAP. A three-point partial R-star folds
  onto an edge as a HE on all its irreducible edges/singletons; no
  injective homomorphism can place that star in a degree-one matching.
  Alternatively, a homogeneous pure structure with one singleton named
  sort and one infinite other sort has AP, but two source singleton-sort
  points cannot inject into its sole such target point.
- An injective HE is not globally induced: two isolated partial source
  points can inject into an edge in the random graph. Its singleton
  irreducible pieces embed, while a missing source edge is added.
- Separate image types are weaker than a joint-union type. In an infinite
  pure set, map two source points constantly and distinguish their
  singleton factors. Each singleton image type survives an injective
  replacement, but their joint image grows from one point to two.
- AP without semantic CCO does not force triangle fullness. The age of
  one-colour K3 has AP; all <=3-point parts of K4 belong to it. Every
  K4 cycle has a homomorphism into K3 and its AP fans may identify
  nonadjacent vertices, yet the COMPLETE K4 cannot map into K3.
- COMPLETE input is substantive. The age of K2 has AP and homomorphic
  CCO by bipartiteness. A PARTIAL C5 has no displayed triangle but cannot
  complete. This refutes only the weaker partial-triangle-consistency
  claim: its partial triples are not complete K members as A07 requires.
- With F(0)=F(1)=1, deleting 1 from {0,1} is not closed. Therefore
  the specific clone-over-deletion proof cannot be transferred unchanged
  to functional signatures. This is a proof-step boundary, not a
  refutation of independent unary injectivization theorems under their
  own hypotheses.

All five HN/HKN receiving bindings, prior source scope gates and the
overall source-relative EPPA candidate are unchanged. Private registration
does not release B038, alter public Work coordination or implement a cache.
