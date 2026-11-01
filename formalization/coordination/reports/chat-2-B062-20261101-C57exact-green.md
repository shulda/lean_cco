# B062 — full connected original gate and nonempty exact trace checkpoint (2026-11-01)

Immutable author: `chat-project:cco-chat-2`, actor `chat-2`, project_id 5. Owned B062, draft PR #68, branch `chat/chat-2/B062`; not submitted, not reviewed and not integrated.

## Verified exact-head evidence

- Exact green source head `64a429fef288a09b91f326a2669cdb87829b79b9`.
- GitHub Lean CI [41245883365](https://github.com/shulda/lean_cco/actions/runs/41245883365): **success**, full root build with pinned source/manifest/provider and cache guards, import/source closure, transitive standard-axiom allowlist audit, final audited artifacts.
- Broker request `20261101_chat2_B062_C57exact_64a429_r479_f2d8b7` received **applied**, STATE revision 480, exact Git state blob `588bd057c4a48a49c6966ece64ea3ec845d360d1`, matching B062 head. Live mode remains chat; slot remains occupied.

## Actual source-to-Lean progress

- `CCO/ExactEPGeometry/OriginalConnectedGate.lean`, root imported: `original_gates_constant_on_full_reached` and `original_gates_constant_in_actual_source_phase` quantify over **every pair** of actual `Reached B.source Kroot` groupoid objects and use their actual full `Reached.connectingArrow`, the already-proved `original_gates_equal_across_arrow` and the literal ONE-original-sort equality. They do not assert all original sorts equal for arbitrary sources; the source one-sort condition is explicit for instantiation.
- `CCO/ExactEPGeometry/OriginalArrowCurrentExact.lean`, root imported: `original_full_exact_nonempty_current_trace` and `original_arrow_nonempty_current_trace_exact` prove that the REAL nonempty p,q trace of any original full RAW-exact relation/whole original `Arrow G G`, with truly equal old parents, has an actual current **FullExact** representation. The essential nonempty trace is an explicit witness. They use existing `ExactTraceTransport.old_to_new`, not generic mixed quotient reverse descent.
- Previous independently green C51–C56 pieces remain in the same head, including actual old D from current bridge, actual p²/q² squares, old square under greatest original gate, true original `Arrow G_p G_p`, exact p,q trace of its whole relation, q² gate trace and Gp=Gq by the actual reciprocal current Arrow and E1/E2/E3.

## Open obligations, truthfully scoped

This green checkpoint is **not** full C57–C58: the nonempty original arrow trace has proven current FULL exactness, but four whole current `Arrow` laws (left/right/source/target) are not yet closed. The next author WIP module `OriginalArrowReverseBridge.lean` is published on the same PR with all four explicit guarded typed TP proofs; it is **unverified** until its own exact-head green CI. Then construct the bidirectional classification for **ALL** actual `Reached` homs, not a generating subset. Further B062: C59–C64 final labels' maximal exact kernel, C65–C105 actual AP-only quotient tower/finite age/phase correction, C106–C112 diagnostics, all selected source theorem and actual provider/consumer closure plus external non-author review. No new axiom, sorry/admit, source/toolchain/pin change, original/quotient SAP, quotient group-action section, or premature merge.
