# Shared decisions

This ledger records decisions that another project must be able to discover.
Routine local implementation details belong in the numbered project report.

| ID | Decision | State |
|---|---|---|
| D001 | One public repository, one Lean/Lake project, numbered equal-status receiving projects; this preparation project owns mathematical allocation. | Agreed with author, 27 October 2026. |
| D002 | Start only Project 1 with B001; test proofs, a consumer and the reporting/integration round trip before adding Project 2. | Agreed with author. |
| D003 | Packages cover substantial connected mathematics; module `T` tasks and individual lemmas are internal milestones. | Agreed with author. |
| D004 | Workers notify the author on completion/blocker/scope change; the author brings the matter back to the preparation project. | Agreed with author. |
| D005 | RAW represented composition and STRONG three-distinct-vertex composition have separate types/operations and explicit conversion lemmas. | Mathematical requirement of the pinned source. |
| D006 | Public destination is `shulda/lean_cco`. Initial Lean/mathlib release is 4.34.1, mathlib commit `d13f23b723b8a846827a245b89c10fc7d3f11612`, with a locked transitive manifest. | Coordinator supplies the initial public scaffold; live CI status is in Actions. |
| D007 | One CI job per main push/PR update; complete matching Mathlib cache, toolchain cache, no whole-workspace cache; transitive axiom audit on CCO. | Adapted from the existing working Lean repositories; see public `BOOTSTRAP.md`. |

## B001 accepted shared API

These records describe the accepted implementation at integration commit
`34b7f1b055788dcf1c134f07fd6a89c123189a82` (main CI 40533022306).

| ID | Decision | State |
|---|---|---|
| D008 | Named sorts are a finite index type `ι` with actual nonempty carriers `X : ι → Type`; tagged real points are `Sigma X`. `AtomicSource S` has finite typed diversity palettes `S.Atom i j`, typed involutive converses and symmetric same-sort atoms; `S.colour` returns `none` **exactly** on actual tagged equality. `none` is not a diversity atom. | B001 accepted, [implementation](https://github.com/shulda/lean_cco/blob/2d526753eff323264cfb2e3be46cf9ebba2c91ce/CCO/Atomic.lean). |
| D009 | `TRel X i j` is an equality-inclusive represented relation; `TRel.ident` is real identity and `TRel.comp` witnesses may repeat vertices. `RawWord` has a genuine empty loop word and erasable identity letters. `PositiveWord` is nonempty and diversity-only; `S.diversityGuard` converts represented RAW output to typed STRONG menus. The full positive guard equivalence needs actual SAP/homogeneity, not CCO. | B001 accepted, [RAW words](https://github.com/shulda/lean_cco/blob/2d526753eff323264cfb2e3be46cf9ebba2c91ce/CCO/RawWords.lean), [STRONG bridge](https://github.com/shulda/lean_cco/blob/2d526753eff323264cfb2e3be46cf9ebba2c91ce/CCO/PositiveWords.lean). |
| D010 | `FiniteInduced` denotes a finite complete actual real subset; `InducedEmbedding` preserves all typed optional pair colours. `PartialDiagram` is a finite simple diversity-constraint diagram with missing edges; `DiagramHom` may collide vertices, while `DiagramHom.IsInjective` asserts genuine tagged-point injectivity. `HomogeneousSource`, `AgeSAP` and `SemanticCCO` remain three distinct hypotheses/interfaces. | B001 accepted, [finite API](https://github.com/shulda/lean_cco/blob/2d526753eff323264cfb2e3be46cf9ebba2c91ce/CCO/Finite.lean). |
| D011 | Source automorphisms use one group `G` with compatible actions on all original carriers and the canonical action on `Sigma X`. Actual pair homogeneity, same-sort pair flips, SAP real-point/edge gluing and stabilizer orbit infinitude are **proved from** explicit homogeneous-source/SAP hypotheses; no new global mathematical axiom or CCO/NR2 shortcut. Boolean all-coordinate `S.PC` with typed Peirce rotations is in `CCO.StrongGeometry`; no B003 PC fixed-point theorem is imported. | B001 accepted, [source-level bridges](https://github.com/shulda/lean_cco/blob/2d526753eff323264cfb2e3be46cf9ebba2c91ce/CCO/RawSource.lean), [STRONG API](https://github.com/shulda/lean_cco/blob/2d526753eff323264cfb2e3be46cf9ebba2c91ce/CCO/StrongGeometry.lean). |
| D012 | M4's `ActualSpan` is a finite set of actual base vertices with two distinct roots; its canonical factor vertex sets meet exactly in that base. `FactorSpanEmbedding` has independent induced embeddings of both factors and requires the displayed base map to cover the **whole** target designated base; only the source's literal typed colours determine the domain. No SIR theorem or arbitrary base-enlargement naturality follows. | B001 accepted, [consumer](https://github.com/shulda/lean_cco/blob/2d526753eff323264cfb2e3be46cf9ebba2c91ce/CCO/BasePaths.lean), [factor embeddings](https://github.com/shulda/lean_cco/blob/2d526753eff323264cfb2e3be46cf9ebba2c91ce/CCO/SpanEmbedding.lean). |

The public import closure is `CCO.lean` and the source-to-Lean export map
is in `formalization/coordination/reports/1.md`. B001 uses unchanged
Lean 4.34.1 and mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`.
The first comprehensive checked implementation was
[`2d526753`](https://github.com/shulda/lean_cco/commit/2d526753eff323264cfb2e3be46cf9ebba2c91ce)
(CI [40524908142](https://github.com/shulda/lean_cco/actions/runs/40524908142),
successful; 8,956 Lake jobs, 647 audited `CCO` declarations).
Future changes to an accepted shared API require a new decision row preserving
the original.


## Autonomous coordination — supersedes allocation parts of D001/D004

| ID | Decision | State |
|---|---|---|
| D013 | After reviewed B001 acceptance, projects may claim the lowest released package with all dependencies ACCEPTED. Non-force exact-ref CAS on the coordination ledger prevents double allocation. | Author approved 27 October 2026; protocol 2. |
| D014 | Main BOARD is the contract catalogue; AUTONOMY is the release policy; coordination-branch STATE is the only live assignment/review/acceptance authority. Do not merge the ledger branch into main. | Replaces the old main-board live-allocation convention. |
| D015 | A submitted worker may take another independent package. A different project/coordinator reviews the source/API/providers/consumer; all merges serialize, and acceptance needs green resulting main CI/audit. | Author requested autonomous progress and peer integration. |
| D016 | Initially register projects 1 and 2. Release B002–B019 subject to accepted dependencies; larger parallelism follows a successful two-project integration checkpoint. Source/theorem, breaking API and toolchain changes remain coordinator decisions. | Concrete release policy in AUTONOMY.json. |

## One Work team — supersedes organizational parts of D013/D015/D016

| ID | Decision | State |
|---|---|---|
| D017 | Original formalization projects 1/2 stopped; one Work team (project 3) takes both claims without resetting WIP, original authorship, current heads, PRs or ledger history. | Explicit author authorization, 28 October 2026; protocol 3. |
| D018 | Two unresolved active batches by default; all claimed states count. Third only for concrete independent active work, fresh accepted dependencies and durable current-head evidence. Repairs/completion have priority. | Author-approved organizational migration. |
| D019 | Separate actual non-author review role, with original/new authorship and stable identity checks; project renaming is insufficient. After valid independent exact-head approval, integrate automatically using one lock for math and infrastructure, exact PR CI/audit and green resulting main before acceptance. | Author-approved; mathematical contracts/source/toolchain unchanged. |
