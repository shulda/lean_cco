# B037 — actual unary HN providers and typed source assembly

The mathematical implementation covers the frozen B037 contract: twelve
definitions D01–D12, all 47 claims C01–C47, six tasks and five source exports.
The mathematical source remains `490c3f36d85db5a0b3ced0598e6c431825254ec5`,
`sections/unary_hn_transfer.tex`. Preparation statuses and contracts are
historical immutable inputs; this receiving report records their actual
discharge without changing them. Main B036 was merged with history preserved
from `8a8e2f9e73e4bdcb0101259416238c8f9ab4429b` before assembly.

## The three actual published-input bindings

| Input | Actual receiving proof |
|---|---|
| E01, HN Theorem 2.19 | `Native.allOrderedModels_ramsey` in `OrderedAmbient.lean` invokes the actual `StructuralRamsey.Structure.allThoseRamseyClasses_theorem_2_19_partialFunctions`. The compatible provider is an exact 106-module subtree, registered and separately cached. `Raw.language`, the literal sort/graph codec and the actual ordered-embedding equivalence bind it to the typed source. |
| E02, HN Proposition 2.6 | `EPPABridge.unary_completionIffStrong` in `EPPABridge/Completion.lean` constructs the genuine profile-restricted positive-language class and uses accepted `AllThoseEPPA.MainTheorems.completionIffStrong`. Full class, embedding, irreducibility, nullary/empty and HE transports are proved. `Native.unary_injective_completion` yields injection plus HE, without global inducedness. |
| E03, original functional HN Theorem 2.11, unary case needed here | `Native.original_unary_locally_finite_ramsey` in `IteratedTransfer.lean` proves the original actual closed-substructure local-finiteness theorem by finite Hales–Jewett/Picture/rank construction. Its hypotheses are precisely actual unary language, hereditary SAP K, inclusion in an irreducible Ramsey ambient and original local finiteness. No canonical-target/tree/provider schema is supplied. Revised relational Theorem 2.18 is not substituted. |

E03 constructs the admissible free class `admissibleClass K` from actual
singleton-valued diagrams whose EVERY irreducible is an actual K member.
`UnaryFunctions` proves a unary HE reflects definedness on one-generated
closures, so literal images of actual closed subsets remain closed.
`ClosedLocal` transports the exact original finite subset cardinality.

`MarkedCompletion.completion_with_mark` extends an ordinary completion to
an entire actual K mark, using hereditary membership and genuine SAP.
`MixedCompletion` handles a mixed closed test in a binary attachment:
each literal projected side image is smaller because the test has a point
outside that side. The predecessor control completes these actual smaller
closed images. Their completions are aligned over the SAME whole A mark
and glued using actual class SAP. The overlap is not assumed irreducible
or globally injective; full induced embeddings on the actual K marks are
derived. `ClosedAmalgam` proves the exact closed restriction and free HE
gluing used here.

`InitialCompletion` constructs actual completions of initial B pictures,
including empty overlaps and nullary diagrams. `StageInvariant`,
`PictureInvariant` and `RamseyInvariant` carry an auxiliary predicate
through the actual finite attachment, Hales–Jewett core and canonicalization
proofs. Their generic hypotheses are DISCHARGED in `RankStep`, which raises
the closed-completion bound from m to m+1. `PartiteTransfer.RankStage`
iterates these passes on each changing ACTUAL control, composing all maps
to the ORIGINAL ambient witness. It uses n+1 positive passes to handle an
original zero cutoff, then weakens to the original n before invoking the
given local-finiteness implication. Finally `arrow_of_HE_completion`
transports all embedding colors using actual irreducibility of A and B.

## Complete source-to-Lean map

| Claims | Constructed implementation |
|---|---|
| C01–C02 | `RawEncoding/PairCoverage`: actual unary reachability or a positive binary tuple excludes exclusive points in a proper free split. The source export retains totality. Additional relation arities are allowed. |
| C03 | `UniversalEdge/TupleSupport.relation_tuple_hull_irreducible`: actual generated hull of the WHOLE positive tuple, all arities, repetitions and nullaries. |
| C04–C10 | `UniversalEdge/{Basic,SameMap}`: HE restriction to actual closed pieces, completed-map rigidity, same-map expanded embeddings, loop rejection and global positive-edge preservation. The SAME given map is retained. Both sufficient rigidity conditions are proved. |
| C11–C12 | `RawEncoding/{Basic,Free}` and `TypedTransferBasis`: same-carrier graph/sort/relation encoding, actual full embeddings/closed subsets/closures/free splits both ways; raw root decoding and genuine hereditary SAP/irreducibility transfer. |
| C13–C14 | `OrderedAmbient` and `OrderedRigidity`: arbitrary total order makes all ambient objects irreducible; genuine E01 all-model Ramsey; actual finite ordered embedding rigidity and equal-range uniqueness. |
| C15 | `Ordered/{Shuffle,Amalgamation}`: actual whole-base finite cut/side/rank shuffle on the entire SAP host, with empty roots and extra target points included. |
| C16–C17 | `Ordered/Forget`: adding order preserves old irreducibility; forgetting ordered HE completion keeps the SAME old closed diagrams/maps and cardinality. No converse irreducibility claim. |
| C18–C22 | `RawEncoding/Typing`: actual raw one-generated membership forces unique sort, partial function domains/values and totality; EVERY positive old tuple's irreducible hull forces all coordinate types. Raw candidate typing is proved BEFORE applying the typed obstruction bound. |
| C23–C26 | `Obstruction`, `OrderedObstruction`, `RawEncoding/Obstruction`: actual old irreducibles in K; apply the given restricted integer N; restore only order on the SAME closed witness set; exact small-substructure completion contradicts its noncompletion. Negative N is retained. |
| C27 | `EPPABridge/Completion`, `Ordered/Completion`: genuine E02 old injective HE into an actual finite K member. |
| C28–C30 | `OrderCycles` proves displayed closed walks impossible under the possibly collapsing given ambient map and no new cycles under the DIFFERENT global injection. `Ordered/Completion` builds a whole-target total extension from a WithBot label agreeing with that ambient map on the injection range, including all extra points and empty carriers. |
| C31–C33 | `Ordered/Completion`: actual expanded irreducible membership first makes its old reduct an actual K member; class irreducibility then lets the old HE embed it. Its actual total source order gives reflection. The result is globally injective ordered HE, without global reflection on reducible source tuples. |
| C34–C36 | `LocalFiniteness`, `NativeTransfer`, `TypedTransfer`, `Source`: ONE `Int.toNat(max 1 N)` cutoff for EVERY ambient C0; actual E03 plus E01/E02 gives Ramsey in the larger raw all-model ambient; literal typed ordered arrows are read back. |
| C37–C39 | `TypedTransferBasis.b034_singleton_and_total`, `RawEncoding/Obstruction.restricted_of_direct`: use ONLY accepted B034 actual C20/C21, supported by independent C19. The direct premise PROVES the main restricted premise. `Source.typed_direct_irreducible_unary_hn` exports both uniform local finiteness and Ramsey. |
| C40–C41 | `RawEncoding/Obstruction.allIrreducible_of_binary`, `TypedTransfer`, `Source.typed_abstract_unary_hn_ramsey`: derive completed irreducibility from actual positive binary coverage, retain arity≤2 and the supplied direct N-bound. |
| C42/C47 | Exact actual membership and closed tests are explicit in the raw typing, `RestrictedObstruction`, `DirectObstruction`, `ClosedSmallCompletable` and principal source signatures. There is no bound on arbitrary malformed diagrams or generated closure sizes, nor an inheritance claim for a typed Ramsey subcategory. |
| C43 | `UniversalEdge/Boundaries.rigidity_cannot_be_omitted`: concrete empty-language Bool→Unit old HE collapses a universal edge. |
| C44 | `UniversalEdge/{GlobalCollapse,ReductBoundary}`: concrete rigid complete-R class still allows a globally collapsing partial-source HE; separate actual two-sort old diagram is reducible while its edge expansion is irreducible. |
| C45 | `UniversalEdge/Boundaries.injective_HE_not_globally_induced`: actual two isolated points inject by HE into a complete graph, adding the missing pair. |
| C46 | `ObstructionBoundaries/{Basic,Path,FreeSplit,ProtectedPieces,ProperCompletion,ClassLabels,AmalgamPoints,StrongAmalgam,Unbounded}` constructs the genuine complete equivalence-colored hereditary SAP age and ALL n≥4 minimal obstructions. Every proper induced subset has a SAME-carrier injective HE completion; all irreducibles and singleton hulls are actual completed members; every integer N fails. `Consumer.constructed_unbounded_sap_age` consumes SAP, irreducibility and unboundedness together. |

D01–D02 are the actual induced closure/free irreducibility and native/typed
HE, `HasCompletion`, `HasStrongCompletion`; D03 is `expandEdge`/`ExpandedClass`;
D04 is `Raw.language`/`encode`; D05–D06 are `AllOrderedModels`/`OrderedClass`;
D07 is `LocallyFinite`/`ClosedSmallCompletable`; D08 is `linearOrderReduct`
and exact forget proofs; D09 is `transportedRelation` with proved cycle
lifting and whole-target ordered completion; D10 is actual `IrreduciblesIn`
versus `OneGeneratedDomain`; D11 is `obstructionCutoff` and direct/binary
discharge; D12 is the three explicit provider bindings above.

## Source exports and consumers

All five `Source` theorems match the source labels in
`sections/unary_hn_transfer.tex`:

- `typed_unary_binary_irreducibility`;
- `typed_universal_edge_reflection`;
- `unary_hn_irreducible_source_transfer`;
- `typed_direct_irreducible_unary_hn`;
- `typed_abstract_unary_hn_ramsey`.

`Source.OrderedRamsey` colors ALL actual typed induced ordered embeddings.
`Raw.orderedEmbeddingEquiv` and `orderedArrow_encode_iff` construct the
literal-map bijection with native arrows; no representation callback is
assumed. `Consumer.constructed_ordered_ramsey_use` returns an actual entire
typed finite K target with total intended functions and its full Ramsey
arrow. `constructed_strong_local_use` returns an actual typed K target,
globally injective ordered HE, and actual totality at the precise cutoff.

The main/direct hypotheses retain the supplied restricted N-bound and
hereditary completed irreducible SAP class. The binary specialization
discharges irreducibility but retains the direct bound. The universal-edge
lemma is separate and retains explicit completed-map rigidity, with no N
or SAP premise. No CCO, geometric obstruction bound, countability,
homogeneity or global classification theorem is asserted.

## Receiving checks and provenance

This map freezes the whole mathematical implementation; owner pipeline,
exact public PR CI/audit, actual independent nonauthor review and resulting
main CI/audit are separate remaining gates. Local Source/Consumer narrow
build passed 1554 jobs before adding the separate C46 aggregate; its union
is checked at final freeze. No admission or mathematical axiom is introduced.
`CCO.lean` appends EVERY new UnaryHN module after its unchanged accepted prefix.
The Ramsey provider has its own exact subtree/cache guards; accepted EPPA
source/guard semantics and original dependency pins remain unchanged.

Actual mathematical contributors retained: `/root/b030_rank` (native rank
construction, obstruction, principal assembly),
`/root/b030_rank/e03_unary_analysis` (mathematical proof design),
`/root/ramsey16` (provider compatibility/cache, tuple hull/same-map and
finite boundaries, C46 continuation), `/root/frontier16` (E02 and ordered
providers), `/root/workspace_recovery` (new literal typed encoding and
obstruction/ordered-arrow readout), `/root/b036_counterexample` (original
C46 finite network/path proofs), `/root/b037_sap` (actual C46 SAP),
`/root/b037_finish` (final typed consumers, assembly/source map), and `/root`
(coordination, recovery and receiving integration). Recovery source commits
have fresh hashes; no claim is made that old lost local Git objects/logs
survived. Details and narrow receipts are retained in the four stream reports
and `B037-ramsey-provider-cache.md`.
