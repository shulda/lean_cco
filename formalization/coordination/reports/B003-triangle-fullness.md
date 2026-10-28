# B003 independent triangle-fullness checkpoint

Implementation commit: `c4c425a8ad7819a6e4232c2564d42c0881f2ca14`, on
`work/B003-triangle`, preserving original B003 parent
`f140b2caf36d912f9d60f84727ba7674b8b7205a`. This report is a follow-up with
no proof changes. This closes the independent triangle-fullness obligation;
it does **not** declare B003 complete or SUBMITTED.

Source remains `490c3f36d85db5a0b3ced0598e6c431825254ec5`,
`sections/triangle_fullness.tex`, `lem:cco-triangle-fullness`.
No source, mathematical contract, accepted API or toolchain is changed.

## Exact source/API map

- `CCO/StrongExact/AgeAP.lean` adds `CCO.AgeAP`: ordinary amalgamation of
  actual finite induced source structures, requiring only a commuting square.
  The interface has no exact-overlap, freshness or SAP conjunct.
- `AgeAP.extend_tuple_triangle` glues a whole finite actual tuple and one
  actual triangle over their complete two-point edge. `pairInducedEmbedding`
  verifies the full complete base, including diagonal and reversal. The
  prefix may move and a new formal vertex may coincide with non-neighbours.
- `AtomicSource.ageAP_of_homogeneous` separately proves ordinary AP from the
  original finite-tuple homogeneity property by moving one factor with an
  actual source automorphism, then taking its finite union with the other.
  It does not use `AgeSAP`.
- `CCO/StrongExact/TriangleFullness.lean` defines finite induced restrictions
  and `CompleteDiagram.SmallRealizable`: every restriction on a finite set
  of cardinality at most three has an actual source homomorphism. Because
  the input is complete and all distinct-pair colours are diversity colours,
  these local maps are automatically injective and induced; this is actual
  age membership, not partial triangle consistency.
- `trianglesRealizable_of_small` reads the actual three old input atoms.
  `fanRealized_of_AP` inductively glues the complete input's actual root
  chords and successive cycle edges using only ordinary AP. It retains all
  prefix colours and never assumes the prefix is injective.
- `cycleHom_of_AP_triangles` performs the full finite-index readout, including
  the closing edge, reversal and dependent sort transports, to the **actual**
  `CycleHom` type. No abstract graph criterion is substituted.
- `CompleteDiagram.triangleFullness_of_AP_CCO` has precisely ordinary
  `AgeAP S`, `SemanticCCO S`, a **complete** input diagram and
  `A.SmallRealizable`. It applies semantic CCO to the whole input;
  `DiagramHom.injective_of_complete` proves its injectivity from the literal
  diversity edge on every distinct pair. Neither homogeneity nor SAP is a
  hypothesis of this core theorem.
- `triangleFullness_of_homogeneous_CCO` discharges ordinary AP using the
  proved original-source wrapper, independently of SAP.
- `induced_realization_of_AP_CCO` is the hereditary-age membership consumer:
  an actual `FiniteInduced` structure and an embedding of all formal vertices
  into it, preserving the **entire** complete ordered pair-colouring,
  including the genuine logical diagonal through `fullColour`.

The at-most-three premise includes empty and singleton restrictions. The
cycle proof handles cycles of every permitted length, including triangles;
no distinctness assumption on named sorts is imposed. All actual induced
image sets are finite. The theorem instantiates the source's hereditary
class statement in the accepted `AtomicSource` actual-age model; it does
not introduce a separate arbitrary-class Fraisse framework and does not
claim completion of a partial triangle-consistent diagram.

## Local validation and precise limits

Pinned Lean/Lake: `leanprover/lean4:v4.34.1`; manifest Mathlib revision
`d13f23b723b8a846827a245b89c10fc7d3f11612`, unchanged.
The local runtime uses the separately verified process compatibility shim.
Build artifacts are isolated copies of B003+PR5-compatible dependencies;
there are no concurrent writers to this worktree's build directory.

Both new source modules were independently compiled with `lake env lean -o`,
then the updated public `CCO.lean` root was compiled. The transitive
`axiom-audit --root CCO --allow propext,Classical.choice,Quot.sound --json`
reported **1,536 declarations, success, zero violations**, using only those
three allowed axioms. Direct `#print` confirms the core signature above;
`#print axioms` for the core theorem, induced-image consumer and H-to-AP
wrapper each reports exactly `propext`, `Classical.choice`, `Quot.sound`.
The new modules use targeted Mathlib modules and individual tactic imports.

This is not a fresh full Lake build of the old-import original f140 tree:
only the new modules and root were rebuilt against the isolated compatible
compiled dependencies. Root integration must run full Lake build/audit after
combining these files with the shared PR5 import compatibility changes.
No new remote CI run or independent approval is asserted here. The exact
implementation commit was sent to the independent non-author reviewer.
Other B003 C07/provider, PC/completion and source obligations remain tracked
by the batch coordinator and are not discharged by this triangle theorem.

## Subsequent generic export

The distinct arbitrary hereditary-class formulation is now implemented at
`835e21f5a564a8f6eaf32ba387237ca6dd88192e`; see
[B003-generic-triangle-fullness.md](B003-generic-triangle-fullness.md).
It uses actual existential K-targets throughout ordinary AP and class CCO,
with no source-instance or representation premise. The actual-age theorem
reported above retains its original precise scope.
