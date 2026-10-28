# B003 N06 actual PC completion checkpoint — 2026-10-28

Original B003 authorship/head `f140b2caf36d912f9d60f84727ba7674b8b7205a`
and PR #4 history are preserved. This checkpoint is additive to the existing
PR #5 import fix and the consumer-import compatibility checkpoint
`1e0ac1d2547a5a327378a2c5ec8ffb34badeea04`. It does not certify B003 complete.
Source pin remains `490c3f36d85db5a0b3ced0598e6c431825254ec5`.

## Source and actual exports

Read the actual pinned `sections/typed_pc_fixedpoint.tex`, N06 in
`formalization/strong_selectors/PROOF_NOTES.md`, B003 contract C10–C13,
and actual `PCNetwork`, `FinitePC`, `PCConverse`, `PCSoundness`,
`PathSupport`, `PathCycleSupport` and `CycleCompletion` signatures.

`CCO.StrongPC.stable_line_realizable` constructs an actual family of points
in their original named sorts on every injectively enumerated finite formal
line, for any selected surviving endpoint diversity atom in a stable network.
All adjacent real colours belong to their actual network domains. The proof
is an induction through genuine strong triangle witnesses, aligning the
remaining line's literal endpoint pair by original pair homogeneity.
It uses only the original homogeneous action and network stability; no
Helly, SAP, CCO or assumed completion is hidden in this line theorem.

`CCO.StrongPC.stable_cycles_realizable` cuts each genuine `SimpleCycle` at
its closing edge. Nonemptiness and initial singleton refinement retain the
old closing atom. The line theorem supplies the actual typed cycle points;
initial refinement forces every other specified edge's literal original
atom. This covers arbitrary cycle lengths and arbitrary repeated named
sorts, without identifying distinct formal positions.

`strongCompletion_of_stable_nonempty` applies the existing B003 strong
cycle criterion to give `D.HasStrongCompletion` from the actual hypotheses:
original `HomogeneousSource S G`, `AgeSAP S`, `SemanticCCO S`, and a stable
nonempty refinement of the initial network. This is an actual existential
injective `DiagramHom`, not an uninstantiated provider.

`strongCompletion_iff_nonempty_fixedNetwork` combines that construction
with the existing survivor induction. It proves that the actual finite
strong PC fixed network is nonempty on every distinct formal pair iff the
whole original partial diagram has an injective source completion.
The empty/singleton formal-diagram cases are covered: their pair and cycle
conditions are vacuous and SemanticCCO plus SAP supplies the completion.

## Exact boundary

The existing `positivePathBound` quantifies endpoint-separated specified
walks, whereas C12's pinned formula quantifies genuine simple paths.
These definitions were not conflated. No simple-path equality, extension
of every chosen surviving atom, or complete C13 canonical-domain converse
is asserted here. Those remain explicit remaining work, together with the
other independent B003 obligations.

Both public new modules are imported in `CCO.lean`. No accepted signature,
source, toolchain, mathematical axiom or hypothesis was changed. The full
combined root builds successfully (1011 Lake jobs) with pinned Lean 4.34.1
and targeted Mathlib consumers. The local transitive audit uses official
axiom-audit v0.1.2 commit `46024e005996495c65ef609368e11ab39c4222e3` and
accepts only `propext`, `Classical.choice`, `Quot.sound`; its exact declaration
count is recorded in the work-team checkpoint. The local runtime adapter
and cache setup are documented in the separate infrastructure report.
Remote exact-head CI must be recorded on the subsequently combined PR head;
this local checkpoint is not an approval of a later changed head.

## Additive prescribed-pair helper

`CCO.DiagramHom.strongCompletion_preserves_pair_of_SAP` takes an actual
homomorphism already realizing a specified endpoint diversity atom and
returns an injective whole-diagram homomorphism retaining that same atom.
It uses original H and SAP only. The actual atom makes the two tagged real
images distinct, so the literal two-point base can be pinned during the
existing SAP injectivization. This helper is available to the separate
three-root source work; it does not infer a desired homomorphism from
PC or assume any unproved pair-realization provider. The public module
`PrescribedPairCompletion` is root-imported and individually kernel-checks.

The preceding actual PC-completion checkpoint was independently rebuilt
at commit `1d074b5828abc78b7769a6eafe5a7d574cae4bd4`: full 1011-job build
and transitive audit of all 1484 declarations passed the three-axiom allowlist.

## Selected survivor source discharge

The additive `PairEdgeExtension` constructs an actual finite diagram
`D.withPair x y hxy a` with that literal original atom and its typed
converse. `pair_compatible_of_fixed_survivor` discharges compatibility
with any existing label from the actual fixed-domain singleton bound;
`withPair_preserves_old` and `forgetPairHom` retain all old constraints.
Every specified augmented atom belongs to the corresponding old fixed
domain when all those domains are nonempty.

`PairSurvivorCompletion.fixed_survivor_augmented_cycles` proves genuine
CycleHom for every simple cycle of the augmented diagram. If the selected
pair occurs, the cycle is reindexed so this edge is the closing edge;
proved unordered-edge uniqueness shows every other line step is old.
The stable-line witness then preserves each exact old fine atom and the
chosen closing atom. Cycles omitting the pair are handled by the same
old-line argument. This uses the original rotation/uniqueness proofs by
the separate STRONG agent, with their Git authorship preserved.

`CCO.StrongPC.fixed_atom_extends_to_completion` now constructs an actual
injective whole-diagram homomorphism for EVERY chosen fixed-domain atom.
Its hypotheses are exactly original H, SAP, semantic CCO and nonemptiness
of all fixed domains; no completion/Helly/augmentation provider is assumed.
The constructed augmented completion is forgotten back to D without
changing any point or the selected atom. Consequently
`CCO.StrongPC.fixedNetwork_eq_survivor D H sap cco hAll x y hxy` identifies
the actual PC menu with the whole-diagram survivor menu. The reverse
inclusion reuses the already proved survivor induction/greatestness.

This closes the chosen-survivor extension part of C12 and supersedes that
item's earlier OPEN status above. The exact equality with the intersection
of GENUINE SIMPLE path profiles remains OPEN; the earlier definition of
`positivePathBound` on endpoint-separated walks is still not conflated
with that source formula. A separate finite-line/simple-path bridge is
being implemented by the STRONG agent. Other remaining B003 obligations
are assessed from the combined current submission, not this checkpoint.

## Genuine simple-path formula source discharge

`SimplePathFormula.simplePathBound` quantifies exactly
`SimpleSpecifiedPath D x y`, the subtype of old specified positive paths
whose list of ALL formal vertices is proved nodup. The separately authored
`FinLinePath` constructs such a path from every injectively enumerated
specified finite line and proves its vertex list is exactly `List.ofFn` of
that enumeration. Thus no formal simple path is lost, and no arbitrary
endpoint-separated walk is silently treated as simple.

`simplePathBound_augmented_cycles` adds an arbitrary atom of this genuine
bound on its endpoint pair. Every new cycle is rotated, and if needed
reversed with actual typed atomic converses, so the remaining OLD simple
line runs in the bound's own endpoint direction. Its selected atom belongs
to that genuine path's profile; the original H+SAP guarded word semantics
supplies real points for every old line letter and that same endpoint atom.
No fixed-domain membership of this arbitrary bound atom is assumed.
Unordered-edge uniqueness proves the line has no other added edge.
Cycles omitting the pair are read from an existing old completion supplied
by the earlier independent nonempty-PC completion theorem.

`simplePathBound_extends_to_completion` applies the original strong cycle
criterion and forgets the compatible added edge. Every bound atom therefore
has an ACTUAL injective whole-diagram realization. The old one-edge simple
path forces compatibility with any existing specified fine colour.

The exact pinned N06/C12 export is now proved:

```
CCO.StrongPC.fixedNetwork_eq_simplePathBound D H sap cco hAll x y hxy
```

It states equality of the actual fixed domain and the intersection over
ALL GENUINE simple specified path profiles, under exactly original H, SAP,
semantic CCO and nonemptiness of all fixed domains. The no-path boundary is
the typed diversity Top (`simplePathBound_eq_top_of_no_paths`), with no
invented diagonal identity. The proof preserves arbitrary repeated named
sorts while keeping all formal simple-path positions distinct.

Only AFTER that source theorem, `fixedNetwork_eq_positivePathBound` derives
equality with the earlier endpoint-separated-walk bound under the same
source hypotheses. The two path-family definitions remain distinct. This
supersedes the earlier OPEN simple-path-formula statements in this report;
it does not certify other unreviewed B003 obligations or the whole batch.
The original STRONG agent's finite-line, rotation and reversal authorship
is preserved through their Git commits. The new public source module is
root-imported; combined exact-head build, output-byte consistency checks
and transitive axiom audit are recorded in the work-team checkpoint.
