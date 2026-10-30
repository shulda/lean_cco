# B045 — direct c-component CCO proof

Actual implementation identity: `/root/b045_clone_sap/clone_cco`.
Mathematical source: `490c3f36d85db5a0b3ced0598e6c431825254ec5`,
`sections/ramsey_clone_sap.tex`, expanded by `formalization/clone_sap/PROOF_NOTES.md` N04.
The actual source and expansion were read. The mathematical contract is unchanged.

## Exact allocation and proof map

All implementation declaration names below are relative to
`CCO.CloneSAP.CCO`; file names are location breadcrumbs only.

This helper owns `CCO/CloneSAP/CCO/` except the independently implemented
`GenericCycleBlocks.lean`, plus this report. The clone `Basic.lean` source
is the batch owner's proved actual construction.

- D05/C14: `cloneGraph` is exactly the specified c-edge subgraph;
  connected components include isolated vertices. `componentSort` descends
  the original named sort along actual c-paths.
- C15: `old_edge_distinct_components` uses an actual simple c-path plus the
  offending old diversity edge. Atomic exclusivity excludes that old edge
  from the path; `SimpleGraph.Walk.cons_isCycle_iff` proves a genuine cycle of length at least
  three. Its actual clone homomorphism would collapse the old edge's owners,
  contradicting original diversity.
- C16: `old_parallel_labels` joins two actual old edges by disjoint simple
  c-paths inside their components. `twoPathWalk_isCycle` retains zero-length
  connecting paths and proves a real simple cycle. Both paths cannot have
  length zero for two conflicting original labels. One cycle assignment
  projects to equal old ordered pairs, so their literal tagged atoms agree.
- D06/C17: `quotientDiagram` is a finite original diversity-only
  partial graph on the actual connected components. `OldBetween` retains
  original endpoints, specified old edge and exact typed atom. The edge
  choice uses proved uniqueness, not a coherence premise. No equality
  edge or internal old edge is inserted; all isolated components remain.
- C18: `CycleEdges.lean` chooses actual old-edge representatives of every
  quotient cycle and actual simple c-path connectors. Distinct quotient
  vertices force the full connector supports disjoint. `CycleProjection.lean`
  proves literal old-atom readout from the actual realized old edges and
  owner equalities along those paths. `quotient_cycles` assembles
  these disjoint blocks into one genuine simple clone cycle using the
  separately proved `cyclic_blocks` theorem, then projects its solution.
- C19–C21: `cco_injective` applies ONLY the original `SemanticCCO`
  to this actual old diversity quotient. `realize_from_quotient`
  and `lift_owner_assignment` assign globally distinct natural indices
  to all formal vertices. Missing edges are not asserted reflected.
  `cco_forward` discharges the actual clone `SemanticCCO` instance.
- C22: `oldDiagram` inserts only old diversity atoms. Each original cycle
  solution lifts independently upstairs; `cco_reflects` then projects the
  whole upstairs solution. `cco_iff` gives the exact two-way statement.
- C36: empty diagrams, isolated components and arbitrary finite old carriers
  are retained. Only each original named sort's actual nonempty carrier is
  used for fallback assignments outside a displayed cycle.

The CCO proof assumes no old AP/SAP, homogeneity, triangle-definedness,
countability, equality-extended CCO theorem or later Ramsey theorem.
No stronger quotient-cycle/provider callback occurs in the source exports.
The extra injectivity conclusion is only for partial specified-edge
homomorphisms, not induced embeddings of missing edges.

## Verification and preservation

Pinned local Lean 4.34.1, bundled Lake and unchanged manifest are used.
Builds are narrow incremental targets; no duplicate whole-project tests or
axiom audit were run by this helper. Final `lake build
CCO.CloneSAP.CCO.Cycles` passed 1,015 jobs, including the actual complete
CCO forward/reflection theorem and all support. Log:
`runtime/b045-cco-cycles.log`. The separately implemented generic block
theorem was cherry-picked from native `cfb33d2` (local cherry `b68682f`)
without modifying its proved source. Exact-head/main CI and independent
review remain the coordinator's separate acceptance requirements.

Stable checkpoints: `9c16b10` (literal cycle adapters, fresh lifts and
reflection), `1cf3ae8` (actual component obstructions and old quotient),
`2172c0c` (disjoint connector paths), `edeb762` (typed cycle projection).
The final source adds the literal block-cycle instantiation and closes
ALL C14–C22; there is no remaining source provider in this helper's scope.
Work is isolated in physical `cco-b045-cco`, branch
`work/B045-clone-cco-isolated`; old branches and all WIP are preserved.
An initial physical worktree allocation collision was detected before
committing shared work. The helper collected its own process, copied only
its own source to the new worktree and left the other helper's files and
process untouched. All later sources and generated artifacts are private.
