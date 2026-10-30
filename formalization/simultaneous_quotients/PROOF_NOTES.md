# B041 — simultaneous full exact quotients and their exact towers

Frozen source `490c3f36d85db5a0b3ced0598e6c431825254ec5`.
Fourteen definitions, 60 claims and eight tasks prepare FIVE SELECTED
new Foundations I results and ONE new auxiliary equation. The other
three results in `sections/simultaneous_typed_exact_quotients.tex`
and equations TQ1–TQ4 are already prepared: quotient blocks in
`rigid_groupoid` and whole finite axes/linear Goursat in `finite_kernel`.
They remain imports, not duplicate new coverage or implementation work.

Eight precise contracts select only existing proved human claims:

- `raw_exact` C10: nonempty-result exact saturation/meet distribution;
- `rigid_groupoid` C02, C03 and C04 in separate contracts: actual blocks,
  saturated quotient algebra and safe upward exact pullback;
- `raw_exact` C13: heterogeneous exact-ball Helly;
- `raw_exact` C21: individual finite typed joint exact lifting;
- `finite_kernel` C16/C17: whole named finite-axis projection;
- `finite_kernel` C18/C19: conditional linear Goursat/rank count.

The quotient CCO branch uses ONLY the original block result, pure
private-path combinatorics and ORIGINAL semantic homomorphic CCO. It does
not consume quotient homogeneity/AP/triangle fullness, quotient word
Helly, reverse exact descent or a separate typed FullWord criterion.
There is no new published external theorem or discharged Lean binding.

## N01: Reverse exact descent is ONE-original-sort mathematics

**D01/D03/D04; C01–C10.** Here the original source has one transitive
sort and every old binary orbital is symmetric. Every invariant relation
is a union of orbitals, so is symmetric; the product of invariant
relations is invariant and hence symmetric too. Taking converse reverses
the two factors, proving their represented products commute. This is
one-original-sort commutation, not commutation of typed cross arrows.

Let E be full exact, and D nonempty full exact with `E;D;E=D`.
Choose an exact presentation `D=⋂P_alpha`. Nonempty D witnesses every
restriction and all required meet nonemptiness. Imported C10 gives

\[
 D=E;D;E=\bigcap_\alpha(E;P_\alpha;E).
\]

If the restriction list is empty, D is old top and descends to quotient
top directly. No distribution over an empty RESULT is asserted.
For a nonempty old word `P=a1;...;am`, commutation and E²=E give

\[
 E;P;E=(E;a_1;E);\cdots;(E;a_m;E).
\]

Each factor is the full inverse image of one ACTUAL quotient atom by
I02, including quotient equality when the old atom lies in E. I03's
saturated product identity makes the displayed relation the inverse
image of the corresponding quotient WORD profile. For the EMPTY old
word, `P=Id` and `E;P;E=E`, precisely the pullback of the empty QUOTIENT
word. Old Id, quotient equality and unrestricted top are distinct here.

Inverse image commutes with intersections and is injective on quotient
relations because the quotient map is onto. Thus the quotient meet of
these word profiles is exactly D/E, nonempty and full exact. For K≥E
an exact equivalence, `E;K;E=K`, so K/E is an exact equivalence.

This reverse implication retains the one-original symmetric sort and
actual bisaturation. It is not asserted for independent quotient kernels
of several original sorts. Towers below use the SAFE UPWARD direction
instead and have no dependency on this reverse-descent branch.

## N02: Pure private-path cycle decomposition

**D05/D06; C11–C17.** Start with a finite simple base graph with marked
vertices. Private path interiors are formally distinct, individually
simple and shared with no other path. Contract only genuine equality
letters within a path, retain distinct marked endpoints, exclude any
zero-length resulting path and merge identical-colour direct paths.
Zero paths above a base edge are allowed; no path of length zero is.

Every internal vertex has specified degree two, along its own path.
A simple raw cycle entering such a path must follow it all the way
to the other marked endpoint. A cycle entirely internal to private
paths is impossible. Thus the cycle concatenates whole private paths,
and its marked vertices are distinct apart from final return.

If exactly two marked vertices occur, both paths have that endpoint
pair; since the base graph is simple, they lie over ONE base edge.
If at least three occur, their marked sequence is a SIMPLE specified
base cycle, with one path traversed over each base edge. Direct-edge
merging rules out fake parallel-edge 2-cycles. A direct edge together
with a longer private path is a genuine raw cycle.

This lemma is finite graph combinatorics, independent of group actions,
exact relations, source CCO, homogeneity or SAP. The quotient application
derives its normalization premises rather than assuming them away.

## N03: Anchored quotient triangle extension and separate joint homogeneity

**D02/D07–D09; C19–C28.** Q names actual ORIGINAL-G quotient orbitals.
I02 gives their saturated nonempty full exact pullbacks and identifies
quotient equality with E_s. In particular same-sort quotient diversity
blocks are disjoint from E_s. The quotient palette is finite and each
named quotient sort is nonempty/transitive under G.

Take an ACTUAL finite quotient base C1,...,Cn, with distinct vertices,
and a proposed new vertex in sort u whose requested pair orbitals form
realized triangles. For n=0 use a point of nonempty Q_u. For n=1 align
a pair-orbital witness with the literal existing centre using old-group
transitivity. A same-sort diversity request forces a different class;
there is no extra capacity or infinite-quotient assumption.

For n≥2 choose ARBITRARY fixed old representatives b_j∈C_j. Let D_j
be the old block for the requested new-to-centre orbital. A realized
triangle has its two centre classes in the same actual old-G orbital
as C_j,C_k. One original automorphism aligns that pair to the actual
centres. Any old representative z of the transported third class then
satisfies BOTH `(z,b_j)∈D_j` and `(z,b_k)∈D_k`, by FULL endpoint
saturation, independent of the fixed b_j,b_k. Thus the heterogeneous
exact balls with common target sort u meet pairwise.

I05 supplies ONE common old point. Its E_u-class has every requested
orbital. If C_j has sort u, D_j is disjoint E_u because the requested
orbital is diversity, so the new class differs from C_j. Other sorts
are disjoint by tagging. This proves one-point extension over the EXACT
old quotient base. Induction gives triangle fullness, with actual allowed
sorts/pairs and the n<2 cases included. No original or quotient SAP is used.

For homogeneity use a separate argument. Put each Id_s and E_s in the
joint exact structure and regard a pure quotient finite partial isomorphism
as a joint partial map on EXACTLY its displayed quotient vertices. Every
relation there is the SAME actual old-G pair orbital. Add no arbitrary
original representatives or fine pair colours. I06 gives ONE original
automorphism inducing this map. It induces an automorphism of Q, proving
homogeneity; Q is countable as a finite union of quotients of countable
sorts. Its age has AP and JEP: embed finite factors in Q, align the finite
common base by homogeneity, and take the finite induced union for AP;
arbitrary finite images give JEP. This is ordinary AP, not strong AP.
There is no coherent selection of lifts or group section.

## N04: Semantic quotient CCO from old private word paths

**D10/D11; C18/C29–C40.** Take an arbitrary finite partial quotient
diversity diagram whose specified simple cycles have homomorphisms
into Q. Each specified edge has a nonempty full exact old pullback D
by I02. Choose a finite presentation as an intersection of old atomic
word profiles, each containing D.

If D is typed TOP, choose its EMPTY restriction list. That edge contributes
NO private paths, while its marked vertices remain. Its old endpoint
condition is vacuous, and because D is the full inverse image of this
one quotient orbital, arbitrary projected endpoint images satisfy the
original edge. This is not a zero-length equality path.

For each actual restriction delete logical equality letters locally.
A same-sort quotient diversity block is disjoint from E_s, hence old
Id, so a word reducing entirely to old equality could not contain D.
For cross-sort endpoints an empty loop word is ill-typed. Therefore all
chosen restrictions reduce to POSITIVE-length diversity paths. If two
reduce to direct edges, nonempty D lies in both single old atoms, forcing
those atoms equal. Merge them. Attach every remaining path with formally
private interiors, retaining all marked vertices and their sorts.

The resulting old partial diversity graph satisfies N02. Every raw
simple cycle either uses two paths over one quotient edge, or projects
to a SIMPLE specified quotient cycle. For the first case choose one
actual quotient pair realizing that nonempty orbital; for the second
use ONE homomorphism of the ENTIRE indicated quotient cycle supplied by
the input. Within this raw cycle choose ONE old representative for each
marked variable's quotient image. Nonadjacent variables may share images.

Full block saturation puts every adjacent marked endpoint pair in its
old D for those arbitrary representative choices. It therefore satisfies
each defining word profile, including the one traversed by the raw cycle.
Choose actual old walks for its private path interiors independently,
with the FIXED marked endpoints. Together these walks give a homomorphism
of that entire old simple cycle. Different raw cycles can use different
quotient images, representatives and word witnesses; no globally coherent
choices are required before invoking CCO.

EVERY specified old simple cycle is now homomorphically feasible.
Apply ORIGINAL semantic homomorphic CCO to the ENTIRE raw diagram,
including isolated marked vertices. Its homomorphism realizes every
attached defining word. Thus every marked endpoint pair belongs to D;
top's empty list is vacuous, and merged direct paths still provide their
duplicate constraints. Project marked images to their E_s-classes to
obtain the required quotient homomorphism. Nonadjacent collisions remain
allowed.

This branch uses only I02, the abstract private-cycle lemma and original
CCO. It does NOT use quotient triangle fullness, homogeneity, AP, word
Helly, convolution, reverse descent or a typed FullWord-to-CCO theorem.
Combining its result with N03 proves the full simultaneous-quotient theorem.
All counts concern the five SELECTED new results; the existing block
theorem is not silently re-exported as new.

## N05: Exact towers use upward pullback and canonical class flattening

**D12/D13; C41–C49.** The quotient theorem retains countability,
homogeneity, finite complete typed language, named transitivity and
semantic homomorphic CCO. A same-sort block `E_s;a;E_s` is symmetric
by converse, since each old same-sort atom is symmetric. Cross-sort
blocks have paired typed converses. Its named old-group pair orbitals
are also full-Aut pair orbits: old G is transitive within each named
colour, while full automorphisms cannot merge named colours. Thus the
theorem applies again to the CURRENT source and current full exact kernels.

If the next equivalence F_s is full exact in the current quotient,
I04 pulls it back to an old full exact equivalence H_s containing E_s.
This is the SAFE upward direction, not N01 reverse descent and not
factorwise projection of an arbitrary original mixed word.

Define the canonical class map

\[
 [[x]_{E_s}]_{F_s}\longmapsto[x]_{H_s}.
\]

It is well-defined and bijective, equivalently it unions the E_s-classes
inside one F_s-class. The nested class set is a set of earlier classes;
the direct class is a set of original points. They are not literally
the same set until this canonical identification. Both projection maps
from original points commute with it.

The pullback of double saturation of an old atom is

\[
 H_s;E_s;\{a\};E_t;H_t=H_s;\{a\};H_t,
\]

since the H kernels contain the E kernels. This is the direct quotient
atomic block, including equality. Hence the canonical class map preserves
and reflects all typed atomic colours, with their canonical block names,
and is the asserted complete binary structure isomorphism. Induct through
the finite tower (zero stages use identity kernels and identity map); every
total initial pulled-back kernel remains full
exact and contains its earlier kernel. No group map section is constructed.

Every new atom is a nonempty union of prior atoms, so none splits. Old
same-sort equality cannot become diversity. A strict kernel above Id
contains at least one old same-sort diversity atom, which becomes new
equality. Finite total typed diversity rank therefore strictly decreases,
whether directed atoms or converse pairs are counted under one consistent
convention. No other typed palette can create a compensating new atom.

## N06: Apply full-group projection only to ENTIRE finite quotient sorts

**D14; C50–C54.** Q is now homogeneous, purely relational and binary.
Choose any finite selection of ENTIRE named finite quotient sorts and
put Gamma=FULL Aut(Q), R_s=Aut(Q|Q_s). I07 applies to this actual
structure: coordinate projections are onto, actual pair images are
subdirect, and the finite coordinate image consists exactly of tuples
satisfying all actual pair-image constraints. Empty and singleton
selections have no hidden pair constraints.

Only under the extra conditional premise that the intrinsic R_s are
elementary abelian 2-groups, I08 supplies linear Goursat quotient maps
for the pair images. Their equations form the check map Phi, whose
kernel is precisely the actual finite image. Rank-nullity gives
`2^(sum dimensions − rank Phi)`. This counts the finite coordinate IMAGE,
not full possibly infinite Gamma. No elementary-abelian group structure
is inferred from the quotient theorem itself.

The general entire-axis lemma, linear corollary and equations TQ3/TQ4
already live in `finite_kernel`; only their application after the new
quotient theorem is a new source export here. Use full Aut(Q), not an
arbitrary earlier subgroup image, an intrinsic unnamed fibre group or
a pointwise coarse-owner kernel. No original SAP is required.

## N07: Exact boundaries and finite diagnostics

**C55–C60.** For the mixed-word warning, take three original sorts with
two F2 phase classes each and infinite pure clone fibres; name all
ordered-sort/XOR pair orbitals, including logical equality separately.
The structure is homogeneous: an old partial isomorphism fixes one global
phase translation and partial permutations inside pure fibres extend.
It has SAP using fresh clones. Partial XOR constraints are consistent
exactly when all labelled cycles have zero sum; any consistent system
can be realized with fresh clones, giving semantic HOM CCO.

The old word `0:A→B, 0:B→C` has endpoint XOR0. Quotient B by top,
keep A and C equality. Both projected edge relations are total, so
their projected word product is ALL A×C, strictly larger. Its old XOR0
endpoint relation nevertheless remains a named ATOMIC A-C quotient
relation. The example refutes factorwise mixed WORD descent, not all
conceivable multi-sort exact descent. Top is full exact as an empty
restriction list; equality as an empty word, so these cuts meet the
claimed scope.

For the owner-kernel warning, the fine two-phase quotient on two clone
sorts U,V has full group diagonal C2 because of cross XOR. Coarsen U
to singleton and retain V phases; the coarse full group is C2 and the
fine/coarse map is injective. Its pointwise kernel is therefore trivial,
while the intrinsic U phase fibre group is C2. The phase-equivalence
cuts are full exact: within an infinite phase clone fibre the square of
the same-phase diversity atom gives phase equality, including diagonal.
Top coarsening is exact too. This does not contradict entire-axis
projection, whose actual cross pair group is correctly diagonal/subdirect.

The pure quotient joint lift never adds arbitrary representatives to a
partial map. Individual lifting does not construct a coherent group
section; HOM completion does not assert injection or SAP. Formal private
vertices remain private even if their REAL images coincide. Anchored
quotient centres instead remain distinct by their required diversity
atoms. Nested quotient classes use canonical flattening, not literal
set equality.

The control script independently enumerates finite private-path cycles,
actual quotient blocks/products, one-sort exact presentations, mixed
word projection growth, tower class/atom maps and rank loss. Its finite
axis controls distinguish full binary automorphism groups from a chosen
proper earlier action, and a separate phase owner-kernel control shows
the intrinsic-binding failure. A proper-subgroup example is explicitly
outside the main theorem's FULL original source action.

These are bounded diagnostics, not proofs of infinite homogeneous
CCO/SAP, general Helly, global exact descent or compiled Lean. All 93
frozen source hashes, existing five HN/HKN receiving bindings, provider
cache plan, prior source qualifications and source-relative EPPA status
remain unchanged.
