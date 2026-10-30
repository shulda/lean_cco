# B040 — actual invariant transport and canonical return

Source `490c3f36d85db5a0b3ced0598e6c431825254ec5`, selected file
`sections/typed_invariant_quotient_transport.tex`, blob
`3895b17d7d0176a74d6f69c39e4e22d9cdba5715`. The frozen package contract,
all source files, mathematical dependencies, existing accepted APIs,
toolchain, manifest and workflow remain unchanged.

Implementation authors are `/root/b040_transport`,
`/root/b040_transport/shared_actions` and `root`. The latter supplies the
actual pure-equality nondefinability example. The separate final reviewer
has not participated in implementation or design. Effective claim320 is
based on actual green main90feb040df23e2ef7fd18ebc7df3b92ccfc0a8a0.

## Mathematical behaviour and proof DAG

`Rel A B` is an actual predicate on two actual carriers, `compose` uses
an unrestricted existential intermediate point, and `converse` reverses
the two actual arguments. `InvEq G A` comprises ALL invariant setoids on A.
Its complete lattice is constructed from actual intersections; joins are
least common invariant equivalence upper bounds, never falsely identified
with composition or assumed distributive.

The local `Transport E R` stores exactly seriality, coseriality, invariance
and the predecessor kernel condition. `typed_quotient_transport` derives
the two serialities from the actual nonempty invariant R and the two
transitive endpoint actions. It then supplies this local structure from
the actual QT1 containment. Its `label_edge` specifies the chosen label
for EVERY actual edge, independently of the internal classical predecessor.
The onto equivariant label has kernel literally `Rᵗ;E;R`; its induced
quotient equivalence has the source-prescribed inverse orientation.

`Transport.intervalIso` is on the entire invariant upper intervals. Both
directions are the actual displayed relational expressions, and both
composites are proved identity. The ordinary quotient correspondence is
also restricted in BOTH directions to exactly the invariant setoids.
Actual meets, covers and all existing arbitrary upper/lower bounds are
preserved. `ProperMeetIrreducible` is the proper binary meet test in the
FULL invariant lattice. The upper-interval/global equivalence is proved,
and `push_meetIrreducible` proves preservation in those full lattices.

Actual composition uses the literal intermediate `T.target` and BOTH
kernel conditions. The composite transport is constructed, its actual
target kernel is proved equal to the second target, and the canonical
quotient maps compose in the stated order after only this proved kernel
identification. No unrelated quotient chart is supplied.

The return branch stores a genuine finite `TypedWord` of actual invariant
nonempty letters. `Return.Bound E p s` is only whole-word containment at a
displayed cut. `prefixTransport` DERIVES its prefix kernel by ONE suffix
witness. Its labels all take values in the ONE original quotient a/E.
`edge_label` holds at every actual factor edge; `factor` DERIVES the next
local kernel condition. `factor_target` gives the literal next prefix
kernel and `step` is the resulting actual factor quotient bijection.

`Return.run` recursively composes those ACTUAL consecutive bijections,
including only the proved literal kernel identifications. `run_label`
telescopes this recursion. The final and initial labels are the original
quotient map on the same carrier, so `holonomy_identity` is equality with
the literal identity function a/E→a/E. Repeated original sorts, n=1 and
identity letters are allowed. The implementation even covers the empty
word, a harmless strengthening of the nonempty-word source statement.

For EVERY invariant coarsening J≥E, `coarser_label` is exactly composition
with the canonical original quotient projection. `coarser_kernel` proves
the corresponding prefix-kernel containment, and `coarser_step` proves the
commuting square for BOTH adjacent canonical quotient projections and
the actual factor maps. All coarser holonomies are identities. No named
exact coordinate or first-order formula is inferred in the generic branch.

The formula branch constructs real Mathlib parameter-free first-order
formulas, with actual existential intermediate variables and their exact
semantics. Sort tagging forces intermediate points to have their actual
typed carriers. `Transport.target_relation` identifies the actual constructed
kernel with that formula's relation, and `target_has_formula` attaches the
separate formula gate. In the intended finite named pair-orbital source,
the gate is fully discharged by a literal finite disjunction of original
named pair colours using original pair homogeneity. The signature is finite
in total; its none names are proved to be logical equality with sort guards.
The same construction supplies EVERY prefix and EVERY invariant coarsening
in that intended source. See `work-B040-definability.md` for exact syntax.

The two action results REMAIN the accepted B001 implementation in
`CCO.GroupActions`/`CCO.GroupQuotient`. New consumer modules document the
full proof branches and boundaries without moving or rewiring any existing
API/consumer. In particular they prescribe group ELEMENTS, use left kernel
correction, saturate FULL orbitals before diversity restriction, and retain
the same-root bijective graph exception even across different output sorts.
See `work-B040-shared-actions.md` for its exact map.

## Source and equation exports

| Source label | Actual receiving declarations |
|---|---|
| `lem:typed-quotient-transport` | `typed_quotient_transport`, `actual_transport_consumer`; `Transport.quotientEquiv`, `intervalIso`, `composite_quotient`, `push_meetIrreducible`; separate `Transport.source_target_has_formula` |
| `lem:foundational-typed-return-holonomy` | `canonical_return_identity`, `every_prefix_consumer`; `Return.prefixTransport`, `factor`, `step`, `run`, `holonomy_identity`, `all_coarser_holonomy`, `coarser_step`; separate `source_return_every_coarsening` |
| `lem:prescribed-action-point-lifting` | Unchanged shared `CCO.GroupActions.prescribed_action_point_lifting`; explicit `SharedActions.shared_point_lifting_consumer` and left correction/direction proofs |
| `lem:foundational-orbital-pullback` | Unchanged shared `CCO.GroupActions.orbital_pullback` and `CCO.GroupQuotient`-file API; explicit `SharedActions.saturation_of_any_root_witness`, `same_root_empty_diversity_iff`, `empty_typed_diversity_forces_same_sort`, `empty_diversity_orbital_unique` |
| `eq:typed-transport-kernel` | `Transport.kernel`, `Transport.label_edge`, `typed_quotient_transport` |
| `eq:typed-transport-lattice` | `Transport.intervalIso`, `push_iff`, `pull_iff`, `pull_push`, `push_pull`, `push_meetIrreducible` |

Unqualified main names are under `CCO.QuotientTransport`; `Transport`,
`Return`, `Definability` and `SharedActions` denote its actual nested
namespaces. File breadcrumbs do not invent additional namespaces.

## Complete C01–C50 map

| Claim | Actual Lean proof or construction |
|---|---|
| C01 | `serial_coserial_of_invariant`; `Word.serial_coserial` |
| C02 | `Transport.kernel`, `label_edge` |
| C03 | `Transport.label_surjective`, `label_equivariant` |
| C04 | `Transport.target`, `target_iff`, `target_relation` |
| C05 | `Transport.labelEquiv`, `quotientEquiv`, `quotientEquiv_edge`, `quotientEquiv_equivariant` |
| C06 | `Transport.descend`, `descend_invariant`, `quotientCorrespondence` |
| C07 | `Transport.push_iff`, `pull_iff`, `pull_push`, `push_pull`, `intervalIso` |
| C08 | `Transport.intervalIso_covers`, `push_inf`, `intervalIso_isLUB`, `intervalIso_isGLB`; `meetIrreducible_interval`, `Transport.push_meetIrreducible`, `push_top` |
| C09 | `Transport.composite` |
| C10 | `Transport.composite_target` |
| C11 | `Transport.composite_quotient` |
| C12 | `InvEq` full complete lattice and unrestricted `Transport.intervalIso` signatures, with no exact/named premise or output |
| C13 | `Definability.transportFormula_realize`, `typed_transport_has_formula`, `sourceFormula_realize`; `Transport.target_has_formula`, `source_target_has_formula` |
| C14 | `typed_quotient_transport`, `actual_transport_consumer` and separate `Transport.source_target_has_formula` |
| C15 | `Word.serial_coserial`, including actual nil identity and repeated sorts |
| C16 | `Return.prefixTransport.kernel`, derived from `Return.Bound` and one suffix witness |
| C17 | `Return.prefixTransport` with `Transport.label_surjective`, `label_equivariant` |
| C18 | `Return.prefixTransport.target` with `target_iff`, `target_relation` |
| C19 | `Return.edge_label` |
| C20 | `Return.factor`, `factor_target` |
| C21 | `Return.step`, `step_edge`, `step_label` |
| C22 | `Return.initial_label`, `initial_target`, `final_label`, `final_target` |
| C23 | `Return.run`, `run_label`, `holonomy_identity` |
| C24 | `Return.coarser_bound`, `coarser_label`, `coarser_kernel`, `coarser_step`, `all_coarser_holonomy` |
| C25 | `Definability.typedWord_has_formula`, `source_typedWord_has_formula`, `source_prefix_transport_has_formula`; `source_return_every_coarsening` |
| C26 | `canonical_return_identity`, `every_prefix_consumer`, `source_coarsening_consumer` |
| C27 | `SharedActions.lifted_point_same_fibre` |
| C28 | `SharedActions.left_kernel_correction` and unchanged B001 iff forward branch |
| C29 | `SharedActions.onto_of_all_requests` |
| C30 | `SharedActions.kernel_transitive_of_all_requests` |
| C31 | `SharedActions.shared_point_lifting_consumer`, unchanged B001 iff |
| C32 | `SharedActions.NonfaithfulNonsplit.nonfaithful_nonsplit_requests`, actual Y=B=C2, π=id, actual nonsplit C4→C2 |
| C33 | `SharedActions.kernel_equivalence_invariant` |
| C34 | `SharedActions.output_orbital_has_root_witness`, `output_orbital_pullback_invariant` |
| C35 | `SharedActions.saturation_of_any_root_witness` |
| C36 | `SharedActions.root_orbital_image_exact`, `diversity_pullbacks_partition`, `root_orbital_unique_diversity_part` |
| C37 | `SharedActions.diversity_saturation_of_witness` |
| C38 | `SharedActions.empty_typed_diversity_forces_same_sort` and unchanged shared same-root iff |
| C39 | `SharedActions.nonidentity_kernel_mate_everywhere`, `same_root_empty_diversity_iff` |
| C40 | `SharedActions.same_root_empty_diversity_iff`, injective + onto gives bijective actual maps |
| C41 | `SharedActions.same_root_empty_diversity_iff`, actual graph with independently typed outputs |
| C42 | `SharedActions.graph_pullback_identity`, same-root iff reverse branch |
| C43 | `SharedActions.same_root_empty_diversity_iff`, `empty_typed_diversity_forces_same_sort` |
| C44 | `SharedActions.empty_diversity_orbital_unique`, `disjoint_roots_diversity_nonempty` |
| C45 | `Boundaries.NonDefinability.parity_group_invariant`, `translation_group_transitive`, `parity_not_definable`, `identity_transport_parity` |
| C46 | `Boundaries.empty_kernel_but_no_predecessor`, `Nontransitive.nonempty_invariant_misses_target`, `target_not_transitive`, `full_relation_has_incompatible_predecessors` |
| C47 | `Boundaries.Cyclic.shift_transport`, `shift_not_identity`, `whole_word_not_in_equality`, `unrelated_chart_is_not_identity` |
| C48 | `SharedActions.diagonal_orbital_saturation_boundary`, `diversity_orbital_saturates_diagonal` |
| C49 | `SharedActions.PointHypotheses.empty_domain_requests`, `nononto_point_map_requests`, `onto_without_kernel_transitivity`, `point_motion_does_not_prescribe_group_element` (all four in the same actual PointHypotheses namespace) |
| C50 | `Boundaries.Collapse.universal_transport`, `universal_target`, `singleton_actual_quotients`; full invariant interval API and unchanged shared B001 files/consumers |

## Definitions and tasks

| Definition | Actual representation |
|---|---|
| D01 | `Rel`, `compose`, `converse`, `Serial`, `Coserial`; actual nil word is `TRel.ident` |
| D02 | `InvEq`, its full `CompleteLattice` and upper subtype interval |
| D03 | `Transport.predecessor`, `label`, choice-independent `label_edge` |
| D04 | `Transport.target`, `labelEquiv`, inverse-oriented `quotientEquiv` |
| D05 | `Transport.Covers`, `ProperMeetIrreducible` and actual global/interval equivalence |
| D06 | `Transport.composite` on literal intermediate `T.target` |
| D07 | `Word`, `Return.Bound`, `prefixTransport` for every actual prefix/suffix |
| D08 | `Return.coarser_label`, `coarser_kernel`, canonical `Quot.mapRight` |
| D09 | Unchanged `GroupActions.PrescribedLift`, explicitly applied in SharedActions |
| D10 | Unchanged `GroupActions.orbital`, `pullback`, `kernel`, `saturation` |
| D11 | `SharedActions.diversityPullback`, `typedRootDiversity`, final saturation restriction |
| D12 | Shared `GroupActions.same_point_output_graph` and the literal graph `∃x, q=τx ∧ r=σx` in `SharedActions.same_root_empty_diversity_iff` |

T01/T02 are Core/Lattice/Irreducible/Composition, T03 is Return,
T04/T05 are Definability/FormulaConsumers, T06/T07 are the three
SharedActions modules, and T08 is the actual boundary modules plus these
unchanged-ownership/source-scope records. No task or principal provider remains
open. Finite Python diagnostics remain diagnostics, not theorem providers.

## Validation scope

All new modules have been compiled incrementally by their actual owners under
the pinned Lean4.34.1 and unchanged manifest. The actual owner consumer chain
`lake build CCO.QuotientTransport.FormulaConsumers` passes1176jobs, including
the full elementary return DAG, all action consumers/boundaries, pure-equality
nondefinability, actual FO gate and its attachment to constructed kernels.
No sorry/admit/new axiom or broad Mathlib/Tactic import is present.

13 new modules are appended to the unchanged accepted CCO root import prefix.
The final whole-root incremental `lake build CCO` passed3966jobs, rebuilding ONLY the CCO root in2.2s; all13 new children had already passed their narrow builds. The resulting root has1304 CCO modules (including the root).
Public exact-head/main CI and axiom audit are NOT asserted before they happen;
the coordinator records the actual evidence separately. We have not rerun an
independent duplicate local85-step receiving pipeline. Stable physical slot
reuse preserves accepted cache provenance and disabled Lake artifact restore.
