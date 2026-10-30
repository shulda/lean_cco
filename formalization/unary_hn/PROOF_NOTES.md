# B037 — unary irreducibility and restricted HN transfer

Frozen mathematical source `490c3f36d85db5a0b3ced0598e6c431825254ec5`;
`sections/unary_hn_transfer.tex`. This module prepares five results,
12 definitions, 47 claims and six tasks, with no equation exports.
Its sole mathematical package prerequisite is B034 `unary_support`:
selected C20/C21 and internal support C19, without its optional size bounds.
Source TeX and the separate human edition remain unchanged.

The two elementary local lemmas use no external theorem. The three
transfer results use THREE published HN2019 inputs, with receiving Lean
bindings pending. The pre-existing TWO HKN/local CCO obligations remain
separate; the combined handoff now contains FIVE published-provider records.
No HN theorem or arbitrary obstruction bound is proved by finite controls.

## N01: Pair coverage, actual closure and HE conventions

**D01–D02; C01–C02.** In a nontrivial free decomposition into proper
induced closed factors, each factor has a point outside their intersection.
Choose exclusive x and y on opposite sides. Closedness puts every unary
iterate of x in its own side and every iterate of y in its own side,
excluding both unary-reachability alternatives. A displayed positive
binary tuple joining x,y belongs to neither side, impossible in their
free diagram union. This contradicts the pair-coverage premise.

Arbitrary other relation arities do not invalidate the argument. The
source total-function assumption is retained, although the same reasoning
uses only closure under values already defined. Complete binary orbital
coverage supplies the third alternative; if some graph orbitals are
represented only by functions, they instead give unary reachability and
the remaining pairs must still have positive binary coverage.

Homomorphisms preserve positive relations and defined unary values. A
homomorphism-embedding (HE) must additionally be an induced embedding on
EVERY actual irreducible induced source substructure. Induced functional
substructures reflect domains and retain all already-defined values.
An ordinary completion is a HE into a target class member. A STRONG
completion is a globally INJECTIVE HE. It need not reflect every missing
relation on a reducible whole source. This is the published HN convention;
see N07 for the exact input records.

## N02: Completed rigidity transports the SAME universal-edge map

**D03; C03–C10.** First note a general support fact. The unary closure of
all entries of any displayed positive relation tuple is irreducible: in a
free split the entire tuple must lie in one factor, which then contains
every generator and all their already-defined unary iterates. That factor
is the whole closure, contradicting properness. This includes repeated
entries and an E-loop; a nullary tuple has no argument-typing coordinates.

For an expanded irreducible D in the source C, local ACTUAL membership
gives D in K*, hence its old reduct D^- in K. Forgetting E can destroy
irreducibility, so do not assert D^- irreducible here.

Instead, every intrinsically old irreducible S inside the actual closed
D^- is also such an induced substructure of C^-. The given old HE h
therefore embeds S. Thus h restricted to the WHOLE D^- is an old HE.
Completed-map rigidity, with this source D^- and target H both in K,
makes that restriction an induced embedding. Since E is universally
inequality in D and H*, injectivity preserves and reflects E too. This
proves embedding on every expanded irreducible piece.

To prove global homomorphism preservation of E, take ANY displayed E(x,y)
in C. Its actual generated support is irreducible by the tuple fact, so
is in K*. A possible loop is excluded by its actual membership in this
irreflexive completed class. Applying the preceding restriction argument
to that support gives h(x)!=h(y), hence its E edge is preserved in H*.
Old homomorphism preservation was already given. Together these prove
that the SAME h is an expanded HE.

Rigidity follows if each completed member is irreducible, because an HE
then embeds its entire completed source. It also follows if every
completed homomorphism is an embedding. SAP alone does not imply it.
No global injectivity of h on a reducible partial source is concluded.
The old HE hypothesis already retains any required empty/nullary behavior;
the added positive-arity E creates no B034-style empty-source gate.

## N03: A larger one-sorted ambient and explicit local typing

**D04–D06; C11–C22.** Encode the disjoint typed carrier using unary sort
predicates S_i forming a partition on every ACTUAL typed object. Each
named unary function is a genuine partial map, undefined off its intended
input sort; typed relation symbols become ordinary relations restricted
to their prescribed input sort sequences. Actual closed substructures,
embeddings and free decompositions are exactly the same diagrams/maps in
the typed and encoded presentations. Thus encoded K retains heredity,
old irreducibility and SAP.

Use the LARGER ambient R_all of ALL finite one-sorted models of this
encoded language with a global strict linear order. The ambient may have
overlapping/missing sort predicates, off-sort function values or wrong-sort
relation tuples. This is the literal all-model setting of HN2.19. We do
not silently infer that an arbitrary typed predicate subcategory inherits
Ramsey. Every ambient member is irreducible because its total order joins
each distinct pair. Strict versus nonstrict order is a harmless provider
adapter by adding/removing the diagonal on ordered objects. A finite
linear order has no nonidentity automorphism, so copies and embeddings
give the same arrow here.

The local-finiteness candidate C need not initially be type-correct.
Its membership condition (ii), however, forces that conclusion BEFORE
we apply any typed obstruction theorem:

1. In a RAW partial unary structure, U_x is irreducible independently of
   typing or K: any free factor covering x contains every defined iterate
   and hence all of U_x.
2. Actual membership of this expanded U_x in encoded K^< forces x to
   have exactly one sort, every function domain to agree with its input
   sort and every defined value to have the correct output sort. It also
   forces totality on the intended source sort. No typed B034 theorem is
   invoked on a still-ill-typed candidate.
3. For EVERY displayed old relation tuple, take the closure of ALL its
   entries. The support fact of N02 makes it irreducible, even at higher
   relation arities. Its actual encoded K^< membership forces that tuple
   to have the prescribed sort sequence. Nullary relations have no
   argument-typing constraint. The displayed order is a global relation.

Thus C, after forgetting its displayed order, is a legitimate typed input
for the supplied obstruction premise. This proves the needed adapter
while permitting an entirely unrestricted Ramsey ambient. The main proof
will establish local finiteness even in this larger class.

Arbitrary global orders also give an ordered hereditary SAP class K^<.
For a strong old amalgam, the two orders agree on their entire common
ordered base. In each interval between successive base points, before
the first and after the last, shuffle the two finite factor subsequences
while retaining each factor's order. Empty bases work the same way.
Insert any extra amalgam-host points without changing these comparisons.
The functions and domains are unchanged, so both factor maps remain
actual induced ordered embeddings.

## N04: Restricted obstructions contradict the exact small-substructure test

**D07–D08; C16–C17 and C23–C26.** Fix ANY C0 in R_all and the cutoff
n=max(1,N) BEFORE a test candidate. The published Definition2.8 requires:

- a HE from C to C0;
- every actual expanded irreducible induced substructure of C in K^<;
- a K^< completion of EVERY actual induced substructure of C of size
  at most n.

These are actual functional substructures, hence closed under all existing
values. They are not arbitrary weak induced subsets obtained by forgetting
outgoing domains. No substitution by generated closures with larger sizes
is needed or allowed in the cutoff argument.

Adding a relation preserves old irreducibility: a free decomposition of
the expansion would also be a free decomposition after forgetting it.
Hence each old irreducible D^- in C^- gains an expanded irreducible
induced order restriction, which (ii) places in K^<. Its old diagram is
therefore an ACTUAL K member. Together with N03 typing this puts C^- in
the exact restricted domain of the obstruction premise.

If C^- had no completion, the supplied bound gives an ACTUAL induced
unary-closed noncompletable D^- of size at most N. Restore only the order
relation induced from C on that SAME point set. Functions/domains and
closedness do not change, so this is an actual expanded induced D inside
C of size at most n. Condition (iii) gives an ordered completion of D.
Forgetting its order gives an old HE completion: each old irreducible
piece remains expanded irreducible under the added order, so the ordered
HE embeds it. This contradicts the old obstruction. Thus C^- has an old
K completion. If N is negative, the alleged nonnegative-size obstruction
is already impossible; using max(1,N) still gives the claimed implication.

The supplied N is restricted to sources whose irreducibles are already
completed K members. Nothing here bounds arbitrary malformed unary
cycles or derives N from pair coverage, SAP or closure totality.

## N05: Injective completion, DAG transport and HN Ramsey conclusion

**D09; C27–C36.** HN2.6 applies to the encoded old K: hereditary,
irreducible, SAP, and all function arities one. From the old completion
in N04 it gives an INJECTIVE HE f:C^-->B with B in K.

The given map C->C0 preserves every displayed strict-order edge. Any
directed closed walk, including a loop, would give a strict chain returning
to its starting point in C0, impossible. Thus the displayed order is a
DAG. The map to C0 need not be globally injective for this argument.

The DIFFERENT map f is globally injective. Transport the order edges to
its image in B; any new directed cycle would lift through that injection
to a cycle of C. Add the remaining B points as unconstrained vertices
and take a finite topological total ordering. This produces an allowed
B^<, preserving all displayed comparisons. Global injection is essential
to this transport step.

For each expanded irreducible D inside C, (ii) makes D an ACTUAL ordered
K member. Its old reduct is irreducible because ALL completed K members
are irreducible; this conclusion does not follow merely by forgetting
the order. Therefore the old HE f embeds D^-. The source order on D is
already total. Preserving all those comparisons and injectivity give
reflection too: for distinct points one of the two source orientations
already holds, and strict diagonals stay false. Thus f embeds every
expanded irreducible D.

Combined with global homomorphism preservation, this is an ordered HE,
and its injection makes it a strong completion. It is stronger than the
ordinary completion requested by Definition2.8, not a global induced
embedding of every reducible source tuple.

We have handled every C0 and every candidate with the SAME max(1,N).
Hence K^< is locally finite even in R_all, and therefore in the intended
typed ambient as well. Apply the published HN2.11 to R_all using its
HN2.19 Ramsey input, order-induced irreducibility, and the proved hereditary
SAP/local finiteness of K^<. This yields Ramsey. Ordered rigidity again
identifies copy and embedding formulations. The relational closure-
description Theorem2.18 is not used or substituted.

## N06: Exact B034 import and discharge of the direct hypotheses

**D10–D11; C37–C41.** B034 supplies only selected claims C20/C21 of
`lem:hn-irreducible-forces-unary-admissible`: for a TYPED partial unary
source with every old induced irreducible ACTUALLY in completed K, each
one-generated closure U_x is itself such a completed member, and all
intended unary domains are already total. Internal support C19 proves the
independent one-generated irreducibility mechanism. Its optional m-bound,
term identities and hidden-specific admissibility interface are not imports.

Therefore every source in the MAIN restricted obstruction domain is in
the DIRECT theorem's one-generated-admissible domain. The direct N-bound
then gives exactly the obstruction demanded in N04. This PROVES the main
restricted premise for that instance; it is not an extra independent
hypothesis to assume beside the direct one. Apply the conditional main
theorem with this discharge, retaining the hereditary irreducible SAP class
and the same N. No universal-edge adapter or binary pair cover is required.

For the final variant, positive binary coverage of every completed pair
supplies N01 irreducibility. This discharges the completed-class
irreducibility hypothesis before invoking the direct theorem. Retain the
source arity-at-most-two restriction, although the elementary coverage
proof itself allows extra relation arities. Heredity, SAP and the DIRECT
restricted N-bound are still inputs. Binary coverage does not manufacture
that bound or an ambient homogeneous source, countability, CCO or exact
geometry.

## N07: Primary inputs, existing Lean reference and bounded counterchecks

**D12; C42–C47.** The primary version is
[Hubička–Nešetřil, arXiv:1606.07979v4 (3 September 2019)](https://arxiv.org/html/1606.07979v4).
The local transfer uses exactly the following versioned theorem inputs:

- E01: Theorem2.19, all finite ordered models.
- E02: Proposition2.6, unary completion injectivization under hereditary
  irreducible SAP hypotheses.
- E03: Theorem2.11, locally finite hereditary SAP subclass transfer.

Definitions2.3/2.5/2.8 fix HE, injective strong completion and local
finiteness conventions. They are definitions, not extra theorem providers.
The main source already states the three mathematical inputs; this
package exposes their receiving Lean bindings rather than hiding them.

One exact existing E01 API was inspected read-only:

- Repository `janhubicka/partite-construction`, commit
  `918732dcff88fd1ab9be69f70e4f1d66385106e3`.
- Module `PartiteConstruction.Ramsey.AllThosePartialFiniteModels`.
- Declaration
  `StructuralRamsey.Structure.allThoseRamseyClasses_theorem_2_19_partialFunctions`.
- [Pinned source](https://github.com/janhubicka/partite-construction/blob/918732dcff88fd1ab9be69f70e4f1d66385106e3/PartiteConstruction/Ramsey/AllThosePartialFiniteModels.lean#L113)
  and [successful pinned CI](https://github.com/janhubicka/partite-construction/actions/runs/40521111992).
- Toolchain `v4.35.0-rc3`; single-valued partial operations are represented
  by empty/singleton output fibres. The output remains single-valued, with
  full functional embeddings and arbitrary nonempty finite color types.

This is signature/CI provenance, not an integrated CCO adapter or a receiving
axiom audit. All THREE HN binding records remain pending. No exact E02/E03
Lean declaration was verified, and no revised relational2.18 declaration
is falsely relabeled as the original functional2.11 route. The existing
TWO HKN/CCO binding records remain separate: FIVE combined records now.

Finite controls compare actual closures, free splits, maps and order
extensions, and exercise these boundaries:

1. With empty old language and K all finite sets, a two-point constant
   map is an old HE because old irreducibles are singletons. Universal E
   makes its edge collapse to a diagonal. Rigidity cannot be omitted.
2. Even with rigidity, a reducible partial source need not map injectively.
   For complete irreflexive R-graph K, two isolated points can map constantly
   to a singleton, remaining old and expanded HE. Conversely two named
   sorts with at most one completed point each give rigid completed maps
   but a reducible old two-point structure; its universal-E expansion is
   irreducible. This is why the old reduct's irreducibility is not assumed
   in N02.
3. A displayed E-loop is rejected by actual membership of its irreducible
   singleton-generated support. Taking only endpoints instead of their
   closure is invalid when defined values leave that pair.
4. An injective HE from two isolated points to a complete two-point
   irreflexive R graph is STRONG but globally adds the missing R pair.
   This distinguishes the actual HN2.6 output from global inducedness.
5. Completed equivalence-colored networks have R on same-class distinct
   pairs and B on different-class pairs. They form a hereditary SAP class
   of complete binary irreducible networks. For every n>=4, specify an
   R path on n vertices and a B edge between its endpoints. The R chain
   forces both endpoints into one equivalence class, contrary to B, even
   under a homomorphism. Every proper induced substructure completes by
   assigning each R-connected component one equivalence class and keeping
   its points distinct. Its old irreducibles are completed edges and
   singletons, so all singleton diagrams are admissible. Thus these are
   unbounded minimal obstructions despite SAP/coverage/admissibility; the
   theorem's uniform N premise is genuinely additional.
6. Raw candidates with absent/multiple sort predicates, off-sort unary
   domains/outputs or wrong-sort relation tuples fail the relevant actual
   irreducible-membership test. This tests the local typing adapter without
   claiming a typed subcategory automatically inherits Ramsey.

Bounded models do not prove the infinite family of HN arrows or a supplied
application obstruction bound. This private package does not release a
batch, change public Work policy/branches, settle the overall EPPA candidate
or integrate any of the five published-provider receiving bindings.
