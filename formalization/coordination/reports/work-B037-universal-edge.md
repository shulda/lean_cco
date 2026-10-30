# B037 same-map universal-edge proofs and concrete boundaries

Frozen mathematical source 490c3f36d85db5a0b3ced0598e6c431825254ec5.
This stream covers C03–C10 and C43–C45; C01–C02, the typed HN transfer,
ordered/external providers and C46 are separate streams. No source contract,
provider tree or dependency pin changed in this proof stream.

All declarations below use the actual native partial-function structures,
full domain-reflecting embeddings and HE from NativeTransferBasis. The HE
restricts to embeddings on EVERY actual closed irreducible source. There is
no global injection inferred on a reducible incomplete source.

| Claims | Actual declaration | Proof mechanism |
|---|---|---|
| C03 | Native.relation_tuple_hull_irreducible | A positive tuple in a free amalgam lies wholly in one side; closedness then contains its entire generated hull. All arities, repetitions and nullary tuples are included. |
| C04 | Native.HE.restrict_closed | Compose the GIVEN old HE with the full inclusion of the actual closed induced structure. |
| C05–C06 | Native.completed_piece_embedding | Local membership makes the entire expanded irreducible an actual expandedK member. Its old reduct is inK; the old HE restricts there and explicit A04 rigidity supplies a full old embedding. Its injection reflects the universal edge. Old-reduct irreducibility is never asserted. |
| C07 | Native.displayed_edge_no_loop | A displayed loop's actual generated support is irreducible and completed; the completed universal irreflexive relation excludes that loop. No old map or rigidity is needed. |
| C08–C09 | Native.same_map_universal_edge | Every displayed edge uses its actual positive tuple hull and the completed-piece embedding. Functions/old positive relations retain the original preservation laws. The EXACT given vertex map is the expanded HE. |
| C10 | Native.completedMapRigidity_of_irreducible / _of_homomorphisms | An HE embeds its whole completed irreducible source; alternatively use actual completed homomorphism rigidity. |
| C43 | UniversalEdgeBoundaries.rigidity_cannot_be_omitted | Actual finite empty-language Bool→Unit constant old HE; all expanded irreducibles are completed, but the same map collapses an edge to a forbidden diagonal. |
| C44a | UniversalEdgeBoundaries.rigidity_does_not_force_global_injection | Actual completeR class is irreducible/rigid. A two-isolated-point incomplete expanded source has actual completed irreducibles and a constant expanded HE. |
| C44b | UniversalEdgeBoundaries.forgetting_edge_can_destroy_irreducibility | Two unary named sorts with at most one point each give actual completed-map rigidity. The old Bool member has a displayed proper free split; its universal-edge expansion is irreducible. |
| C45 | UniversalEdgeBoundaries.injective_HE_not_globally_induced | Identity from two isolated points to a complete two-point graph is an injective HE, but no full embedding of that source into the target exists. |

The C43–C45 statements construct and inspect actual finite structures, free
amalgams, maps and full irreducible tests. No abstract obstruction/provider
callback certifies these boundaries. The same-map theorem takes only the
explicit A04 completed-map rigidity, A05 local actual membership, actual
completed target membership and the given old HE.

Source files are CCO/UnaryHN/UniversalEdge/{TupleSupport,Basic,SameMap,
Boundaries,GlobalCollapse,ReductBoundary}.lean. Namespace prefixes in the
proof map are CCO.UnaryHN.Native and its UniversalEdgeBoundaries namespace.

Compiled checkpoints: f63ab60836e1155b9dc508d7f68de177a717ba32 (C03),
ede174489ec545605fcf88f39588b5321357067a (C04–C10),
f43ab3bf641e4bec80b28c1fa713ddcbafeeeb8e (C43/C45) and
bff867075724c67ebbd6fe8c28afe3c412264204 (both C44 examples).
The final narrow target ReductBoundary compiled successfully with 1000 Lake
jobs including dependencies and all earlier stream modules. Current logs:
round16-b037-{tuple-support,edge-basic,edge-same-map,edge-boundaries,
edge-global-collapse,edge-reduct-boundary}.log in scratch.
The owning batch performs its one complete source review, axiom audit and
exact-head/main CI after combining all mathematical streams.
