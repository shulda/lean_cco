# B039 — fresh real frames and hereditary unary amalgamation

Frozen source `490c3f36d85db5a0b3ced0598e6c431825254ec5`.
Twelve definitions, 50 claims and seven tasks prepare FIVE Foundations I
results and THREE auxiliary equations. The four results in
`sections/unary_fresh_frame_sap.tex` use the hereditary unary SAP criterion
from `sections/finite_orbit_avoidance.tex`; that selected fifth result is
expanded HERE rather than silently imported as an unprepared theorem.
The explanatory fresh-frame remark is supported but is not counted as
an additional numbered result.

The only import is B010 `acl_owner_geometry` avoidance export C03, with
its proved C01/C02 ancestors as explicitly extracted internal support.
Their hypotheses are abstract group action and infinite moving orbits;
none of the other module's CCO/owner geometry enters this package.
All five existing HN/HKN receiving bindings and the external build-cache
plan remain unchanged. This is human preparation, not compiled Lean.

## N01: Actual typed unary closure and pointwise stabilisers

**D01–D03; C01–C03.** Use the disjoint union of the named sort carriers.
A term is a well-sorted finite composition of named total unary functions,
including the identity term on each sort. Every value has ONE generator.
Consequently

\[
 \operatorname{cl}(T)=\bigcup_{t\in T}\operatorname{cl}(\{t\}),
 \qquad \operatorname{cl}(\varnothing)=\varnothing.
\]

The latter equality uses the absence of nullary generators. Finite
singleton closures suffice for finite closures of finite sets. Arbitrary
relation symbols, even nullary relations, add no generated vertices.
Finite unions of actual closed sets are closed.

Every automorphism commutes with every well-sorted term, so
`g cl(T)=cl(gT)`. A pointwise stabiliser fixes all term values of its
fixed generators. Since identity terms include T in its closure,
`G_T=G_cl(T)`; the same holds for the full automorphism group.
Every closure point has singleton orbit, hence
`cl(T) ⊆ dcl_G(T) ⊆ acl_G(T)` and likewise for full Aut(H).
Here acl is defined by finite stabiliser orbits and dcl by singleton
orbits. Do not silently replace subgroup orbits by full-Aut orbits.

## N02: Fresh frames are equivalent to actual closed-base orbit infinitude

**D04/D05; C04–C06.** R is an invariant generating union of real sorts.
Every finite A has a finite real generating cover: choose one real
preimage and a term for each of its finitely many points.

Assume fresh-frame separation. For finite closed A and `u∉A`, the set
`B=cl(A∪{u})` is finite closed. Choose a finite real D with
`A⊆cl(D)` and `cl(D)∩B=A`. Then `u∉cl(D)`. The supplied SAME-G
real-base orbit condition makes `G_D.u` infinite. Term-fixing gives
`G_D≤G_A`, so the latter orbit is infinite too. No homogeneity or SAP
is used in this implication.

Conversely, assume every off-closed-base G-orbit is infinite. Choose
finite real D0 covering A. Under the action of `G_A`, the finite moving
set `S=cl(D0)\A` has infinite orbits. Apply abstract finite-action
avoidance ONCE, with forbidden set `Z=B\A`. A single `g∈G_A` sends
ALL S outside Z. The set `D=gD0` is still real. Its closure is
`g cl(D0)`, contains A because g fixes it, and meets B exactly in A.
Separate moves for different generators would not prove this assertion.
This reverse implication does not use the real-base orbit premise.

For arbitrary finite hidden T, use `G_T=G_cl(T)`. Closure points are
fixed; every point outside has infinite orbit. Thus the equivalent
conditions give `acl_G(T)=dcl_G(T)=cl(T)`. Empty A has the empty frame;
empty moving or forbidden sets are handled by the same avoidance theorem.
No canonical, functorial or simultaneous choice of frames is asserted.

## N03: Expand the full hereditary homogeneous unary SAP criterion

**D06; C08–C17.** The criterion concerns ALL finite induced unary-closed
substructures, including orphan hidden vertices which have no real
representative inside that finite object. It cannot be replaced by a
criterion restricted to point-generated objects. H is countable and
homogeneous for finite induced closed partial isomorphisms; finite
language and oligomorphy are not needed by this argument.

If the age has SAP, fix finite closed A and `u∉A`, and let
`B=cl(A∪{u})`. Repeatedly strongly amalgamate n copies of B over ONE
common A. The images of u are pairwise distinct by strongness. Embed
the resulting finite age object into H and align its base with literal
A using homogeneity. Each B-copy is induced-isomorphic to original B
over A, so homogeneity extends that map to a full automorphism fixing
A. The orbit of u over A has at least n points for every n and is
therefore infinite. Extra points in the finite amalgam do not matter.

For the converse, assume infinite full-Aut orbits outside every finite
closed base. Given an arbitrary closed span, independently embed its two
factors into H and use homogeneity to align the two induced base copies.
View them as actual B1 and B2 over actual A. Apply ONE finite-avoidance
move from `Aut(H/A)` to moving set `B2\A` and forbidden set B1. It
gives `B1∩gB2=A`. The finite induced structure of H on their literal
union is unary-closed by N01. Its factor inclusions are induced and
have exact base intersection, so it is a strong amalgam in the age.
The induced cross relations can be arbitrary; this is not a free
relational amalgamation claim.

Equal stabilisers of T and cl(T), and fixed term values, identify this
closed-base orbit criterion exactly with `acl_H(T)=cl(T)` for EVERY
finite hidden T. In that event dcl also equals cl. This proves the
selected upstream lemma and its equation UA without an external input.

For the source remark, use full Aut(H), invariant named real sorts and
real-base acl=cl. N02 and the criterion give equivalence of fresh frames,
acl=cl on all finite hidden bases and hereditary unary SAP. SAP alone
does not assert anything about the stabilisers of an arbitrary proper
subgroup. If that subgroup ALSO satisfies the real-base premise, fresh
frames do transfer its infinitude; the warning does not deny this.

## N04: Finite semantic term functions in one actual quotient fibre

**D07–D10; C18–C21.** Let G act transitively on named real sort M and
let the named projection `p_J:M→Q` be onto, with actual kernel J>Id.
Fix `x0∈p_J⁻¹(b)`. Evaluation at x0 injects actual term FUNCTIONS
into the finite singleton closure of x0: if two typed terms agree there,
then equivariance and an automorphism taking x0 to arbitrary y make them
agree at y. Output sorts are retained. There may be infinitely many
syntactic terms, but only finitely many distinct functions and values.

The stabiliser `G_b` is transitive on the actual fibre. A global g with
`gx0=y` in that fibre automatically satisfies
`gb=g p_J(x0)=p_J(y)=b`. Conversely fixing b preserves the fibre.
Therefore for EVERY actual term τ,

\[
 G_b\cdot\tau(x_0)=\tau(p_J^{-1}(b)),\qquad
 [J:J\cap K_\tau]=|\tau(p_J^{-1}(b))|.
\]

The index counts actual equivalence classes within a J-class, not
subgroup cosets or a formal division of cardinalities. Transitive G
makes the count uniform between fibres; no kernel commutation, lattice
distributivity or CCO geometry is needed. For unforced τ this orbit is
infinite by the supplied relative-kernel hypothesis. The finite set of
ALL distinct unforced values at x0 is consequently a legitimate moving
set for the abstract avoidance theorem.

## N05: One representative avoids every unforced value and retains forced values

**D11; C22–C27.** Apply avoidance to the `G_b` action, the finite set
of unforced values, and the entire finite forbidden set Z. Obtain ONE
g fixing b and moving every one of those values outside Z. Put `x=gx0`.
Then x stays in the prescribed fibre and ALL unforced term values of x
avoid Z simultaneously.

Every forced τ is assumed to factor as an ACTUAL NAMED unary term
`τ=σ∘p_J`. Its value at x is exactly `σ(b)∈cl({b})`; it is retained
even if it lies in Z. A set-theoretic or definable factor is insufficient.
Any point of `cl({x})∩Z` is some term value and cannot be unforced,
so it belongs to `cl({b})`. Conversely `b=p_J(x)` and named term
composition give `cl({b})⊆cl({x})`. Hence the exact equality

\[
 \operatorname{cl}(\{x\})\cap Z
   =\operatorname{cl}(\{b\})\cap Z.
\]

The identity term has kernel Id_M, so J>Id makes it unforced. Thus
the SAME choice gives `x∉Z`. This also shows that the hypotheses imply
infinite real fibres; one need not add that separately.

Repeat the construction for a finite list of quotient vertices, even
on different real sorts. Enlarge Z by the extra finite hidden set,
earlier representatives and their earlier unforced values. Finite
singleton closures ensure every next request stays finite. The real
representatives are pairwise distinct; forced values may coincide.
There is no claim that all complete representative closures are disjoint.
This entire lemma is independent of homogeneity, countability, finite
language, real-base orbit infinitude and SAP.

## N06: Assemble AFF before invoking homogeneous orbit assumptions

**C28–C33/C36.** For finite closed `A⊆B`, start with the real points
D0 of A, whose closures are already contained in A. Enumerate EVERY
nonreal `b_i∈A` and choose its actual named quotient representation.
Apply N05 successively with forbidden set containing all B and all prior
representatives. The new real `x_i` lies outside B and its singleton
closure meets B only in `cl({b_i})⊆A`. All forced values are allowed.

Let `D=D0∪{x_i}`. It generates every A point: real points are in D0,
and each nonreal b_i is a named projection of x_i. Unary singleton
additivity shows its closure has no other B point. Thus

\[
 A\subseteq\operatorname{cl}(D),\qquad
 \operatorname{cl}(D)\cap B=A.\tag{AFF}
\]

For empty A take empty D; for an all-real closed A take D=A. A finite
closed hidden object need not be internally real-generated: the fresh
cover can lie outside it. No functorial representative choice is used.

This construction uses the named representations, transitive G, finite
singleton closures and the two actual kernel clauses only. It does NOT
use homogeneity, countability, oligomorphy, finite language, real-base
orbit infinitude or an existing SAP statement. The source theorem retains
those structural assumptions for its final homogeneous conclusion;
the DAG separates A11 representations from A09 retained theorem scope.

On each transitive original real sort singleton closure size is constant
by equivariance. Finitely many such sorts give a uniform finite maximum.
This gives a linear bound in the number of real generators, not a
constant bound independent of that number. An empty real-sort family
is vacuous and, with the representations, leaves no hidden vertices.

## N07: Use FULL Aut only for the final hidden-orbit and SAP conclusion

**C34/C35.** The final theorem supplies full-Aut real-base orbit
infinitude, without requiring the smaller G to satisfy that premise.
For finite closed A and off-base u, apply AFF to `B=cl(A∪{u})`.
The resulting real D covers A but misses u. The infinite
`Aut(H/D).u` orbit is contained in `Aut(H/A).u` because term-fixing
fixes A. This is the forward frame mechanism with the FULL group.

Equal stabilisers and fixed term values then give
`acl_H(T)=dcl_H(T)=cl(T)` for every finite hidden T. The homogeneous
criterion N03 gives SAP of the ENTIRE hereditary unary-closed age.
Countability/homogeneity and the finite-language/oligomorphic theorem
scope are retained here. No old real SAP, CCO, triangle geometry,
exact lattice, HN or HKN premise has been imported.

## N08: Derive BOTH kernel clauses from SAP rather than assuming them

**D12; C37–C46.** Now retain the structural hypotheses but drop BOTH
kernel assumptions and the real-base orbit premise. Assume only SAP
for the forward direction. N03 yields `acl_H(T)=cl(T)` for every finite
hidden T, in particular the required real-base equality.

Fix an existing named quotient p_J and actual term τ, and write
`b=p_J(x)`, `v=τ(x)`. If J≤K_τ, τ is constant on the ACTUAL fibre.
Every FULL automorphism fixing b preserves that fibre via named p_J,
so it fixes v. SAP gives `v∈cl({b})`, hence `v=σ(b)` for an actual
named unary term. For any y choose `g∈G` with gx=y. Equivariance gives

\[
 \tau(y)=g\tau(x)=g\sigma(p_J(x))=\sigma(p_J(y)).
\]

Thus equality at ONE real point globalises to the literal named factor
`τ=σ∘p_J`. The local-to-global implication itself needs no SAP; SAP
was used only to obtain that local equality. Do not assume the forced
factor clause while proving its necessity.

If J is not contained in K_τ, some fibre has two distinct τ values;
transitivity makes the actual common fibre-image cardinal r at least
two. Suppose r is finite. The finite set
`V_b=τ(p_J⁻¹(b))` is invariant under FULL `Aut(H/b)`, since both maps
are named, so v is algebraic over b. Meanwhile `G_b` is transitive on
V_b, so some element moves v. Every named unary term value over b is
fixed by G_b; hence v is OUTSIDE `cl({b})`. This contradicts the SAP
closure equality. Therefore the unforced relative index is infinite.
Neither kernel clause nor real-base orbit infinitude was assumed here.

Conversely real-base acl=cl gives full-Aut real-base orbit infinitude
because all closure values are fixed. Together with the two RK clauses
it instantiates the sufficient theorem N06/N07 and yields SAP. This
proves the exact source equivalence and equation RK, quantifying over
ACTUAL named quotients and ACTUAL existing real-source terms.

## N09: Local boundary witnesses and honest finite diagnostics

**C07/C47–C50.** SAP alone gives no orbit conclusion for a proper subgroup:
the infinite pure set has SAP but its identity subgroup has singleton
orbits. This example fails the generic subgroup real-base premise;
SAP plus that premise DOES transfer through fresh-frame separation.

The two kernel failure mechanisms are visible over ONE quotient point.
If τ is forced but has no named factor, v cannot be any named term value
of b: such an equality would globalise as above. Yet FULL Aut over b
fixes v, so it is definable off closure. If an unforced τ has finite
proper index, its finite invariant fibre image makes v algebraic, while
the transitive subgroup supplies a move proving it off closure.

Two countable homogeneous models isolate the mechanisms while retaining
real-base orbit infinitude:

- Let Q be infinite, S a separate matching copy, M=Q×N with infinite
  pure fibres. Name `p:M→Q`, `τ:M→S` and the relational matching
  `E(q,s_q)`, but no unary map Q→S. Then τ is constant on p-fibres
  and has a unique definable set factor. The matched s_q is fixed over
  q but absent from `cl({q})={q}`. Over finite real bases matching
  partners already lie in their closures; off-closure orbits are infinite.
- Let `V→Q` be a two-cover with named fibrewise swap ι, and `M→V`
  have infinite pure fibres. Name τ, `r:V→Q`, `p=r∘τ` and ι.
  Then `cl({x})={x,v,ι(v),q}` and real-base orbit infinitude holds.
  Forced factors exist, but τ has relative p-fibre index TWO. The
  V-pair is algebraic over q outside `cl({q})={q}`. Both V points
  themselves have their permitted quotient representations from M.

The supplied finite controls check closure identities, actual transitive
actions, literal named factors, common bounded avoidance, fresh-frame
intersections and these local obstructions. Growing finite reservoirs
can be exhausted; the script records such cases explicitly. It cannot
prove an infinite index/orbit, homogeneous SAP, or the unbounded theorem.

A nullary generator changes empty closure bookkeeping. A binary function
can generate a new value from inputs in opposite factors, so the literal
closed-union argument and singleton-additive AFF proof do not carry over.
These are boundaries of THIS proof, not blanket impossibility claims for
other signatures. All source TeX and its 93 frozen hashes remain unchanged.
