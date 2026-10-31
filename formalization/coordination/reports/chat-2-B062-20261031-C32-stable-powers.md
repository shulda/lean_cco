# B062 / CCO Chat 2 — C30/C32 stable-power proof checkpoint

Identity: `chat-project:cco-chat-2`, project 5, actor `chat-2`. Sole author of this B062 branch. This is an implementation WIP record, **not** source submission, independent review, acceptance or merge.

## Canonical coordination and exact-head evidence

- Branch: `chat/chat-2/B062`; [draft PR #68](https://github.com/shulda/lean_cco/pull/68). One owned package remains B062 IN_PROGRESS, first claim STATE rev 402. Source pin `490c3f36d85db5a0b3ced0598e6c431825254ec5`, base main `f42f098e852b4cea8cb09b9ada6b1145a6138dd4`; no pin/source/toolchain changes.
- Actual one-stage marked old equivalence C29: PR head `ee57b1b60bfb6410dc3cabe4b70322933ee57f62`; [CI 41194491526](https://github.com/shulda/lean_cco/actions/runs/41194491526) green full Lean + transitive audit, 28,813 CCO declarations, only propext/Classical.choice/Quot.sound; broker checkpoint **applied rev 425**.
- Actual one-stage join C30: PR head `4bcc6ee9a36b6f5d17f1e78d265b0f6c4ce3a912`; [CI 41202338460](https://github.com/shulda/lean_cco/actions/runs/41202338460) green full Lean + source guards + audit, 28,816 CCO declarations with same allowlist; broker checkpoint **applied rev 426**. Module `CCO/ExactEPGeometry/MarkedJoins.lean` proves genuine old exact equivalence join and the current marked-child relational join; input TP witnesses are real diagonal pairs. It does NOT prove current **word exactness**, so full C30 exact-lattice instance remains open.
- Original positive RAW powers C32: PR head `abe7332b8ffea4252e4c76ce87c5fa05d037229e`; [CI 41203009839](https://github.com/shulda/lean_cco/actions/runs/41203009839) green full Lean+audit, 28,831 declarations within same axiom allowlist; broker checkpoint **applied rev 428**. Module `CCO/ExactEPGeometry/OriginalPowers.lean` proves (1) all original positive RAW powers are FULL exact via accepted `ExactCalculus`, (2) monotonicity under old literal Id, (3) finite pigeonhole stabilization using actual accepted `Geometry.finite_fullExact`, and (4) reflexivity/symmetry/transitivity of stable actual old exact power. No stabilization provider, quotient SAP, new axioms or finite-index assumption.

## Current running code after last recorded green SHA

- `CCO/ExactEPGeometry/MarkedPowerLifts.lean`, publicly imported from CCO root at branch head `5f568d945fda89398d44f4067bfafb1057ca1fe2`, is **WIP pending exact-head CI 41203410844** as of this report.
- It aims to discharge the remaining one-stage C32 trace equality: if an ACTUAL old exact D already traces an equivalence on an inhabited real marked child, the real diagonal plus original transitivity puts old Id inside D. Each exact original power still traces the same current equivalence by repeated full source C22 with the required nonempty displayed child witnesses. The stabilized old exact equivalence therefore has literally the same marked trace.
- It is **not** C27/C33 source surjectivity: an existing original exact-domain lift is an explicit input; representing an arbitrary current exact word profile and iterating across all actual tower prefixes remains open.

## Precise remaining full B062 obligations

- C23–C28: actual word length and finite exact menu lifting from the whole current unary refinement to the ORIGINAL source, using `APCharacter.SourceAge.UnarySource`, `SingleStep.successor`, `UnaryReduct` and real canonical original-to-current projections; prove all specified nonempty middle child types and source-to-current exactness, not merely abstract masks.
- C29–C33: build finite SOURCE exact-equivalence lattice (not all invariant equivalences), check original restriction preserves full exactness, meet and join; use stable power lift to obtain surjectivity; iterate across arbitrary prefix histories. `LargestLift.lean` is a green abstract right-adjoint only and must be instantiated to real exact data before C34–C37 source export.
- C38–C64: literal original parity and maximal gate, exact finite type-support joins/meets and common-gate kernel (not an arbitrary quotiented gate).
- C65–C105: full AP-only original exact quotient-safe tower, retained/discarded steps, projected gates/characters, genuine quotient-groupoid and finite-age converse, and terminality. Conditioned I11 bridge cannot be counted accepted before its C82 actual projected gate source instance.
- C106–C112: only source-scoped rank/diagnostics, E>Id on its required branch. All eight source theorem labels and thirteen auxiliary equations with actual I01–I13 provider consumers still require a source-complete submission and independent review.

Existing report/submission seed `formalization/coordination/submissions/B062.md` is stale WIP and must be reconciled before submission. No merge, reviewer approval or submit event has been issued. CI failures before each green exact SHA are WIP, not accepted progress. Author will keep branch commits and this coordination report durable.
