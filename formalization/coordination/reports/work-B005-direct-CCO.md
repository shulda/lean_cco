# B005 C21: direct original-language signed-component completion

Source pin: `490c3f36d85db5a0b3ced0598e6c431825254ec5`.
Implementation author: `/root/direct_cco`. The source/actual homogeneous model
was authored separately by `/root/b005_positive/direct_model`; the shortest-path
parent-separation branch is authored by `/root`. No author is a reviewer.

The source is the actual `Point = ℕ × Bool × ℕ` and the three original symmetric
diversity colours `e,d,n`, with no named sheet/parent predicates added. C21 does
not assume homogeneity, SAP, NR2, an HS, a graph constructor or a CCO provider.
The only input to the completion theorem is the actual partial diagram and a
homomorphism of each of its genuinely specified simple cycles, exactly as in
`SemanticCCO`. Vertex types may live in any universe; their finiteness is the
existing `PartialDiagram.finite_type` field.

## Proof map

* `Direct/Constraints.lean`: the e/d graph consists precisely of specified e/d
  edges. Its Boolean sign is the literal occurrence of `d`, with symmetry
  derived from `PartialDiagram.edge_reverse`. Realizing an e/d edge preserves
  the parent and changes the sheet exactly by its sign.
* `Direct/CycleWalk.lean`: a graph-theoretic `Walk.IsCycle` gives the exact
  `CCO.SimpleCycle` record with an injective `Fin length` vertex map, length at
  least three, actual cyclic adjacency and specified original edges. It never
  treats a repeated-vertex closed walk as a simple cycle.
* `Direct/SignedWalk.lean`: symmetric signs that vanish on simple cycles vanish
  on every closed walk. The proof uses strict length induction, splits a
  nontrivial closed subwalk out of a non-path tail, and handles immediate
  two-edge returns separately. Component reference walks then give an actual
  Boolean sheet potential. The potential theorem works even on infinite
  vertex carriers; no graph-existence theorem is assumed.
* `Direct/CycleConsistency.lean`: unroll each actual `CycleHom` on the simple
  walk's indexed vertices. Telescoping the realized sheet differences makes
  its sign zero; the preceding strict induction supplies zero for all closed
  walks. This proves the consistency premise used to construct sheets.
* `Direct/ParentSeparation.lean`: a specified n-edge inside an e/d component
  closes a simple e/d path to a genuinely specified simple cycle. Its actual
  cycle homomorphism would make the endpoints' parents both equal and unequal.
* `Direct/Realization.lean`: embed the finite component type into natural
  parents and the finite original vertex type into natural fibre indices.
  The point `(component ID, sheet potential, vertex ID)` preserves every
  specified e/d/n edge. Distinct fibre indices prove that the complete real
  realization is injective, including all unconstrained vertices.
* `Direct/CCO.lean`: instantiate the parent-separation premise using its actual
  cycle proof and export direct `SemanticCCO` and injective completion. No
  parent/graph/selector/CCO provider remains in these final exports.

## Boundary cases and validation

Empty vertex types and empty edge sets use the same finite embeddings and
component construction without choosing any global root. Roots are chosen
only inside an actual component, which supplies its own inhabited carrier.
The two-edge return case uses symmetric signing, rather than inventing a
length-two specified simple cycle. `e` edges keep equal sheets but remain
irreflexive because of the distinct fibre indices; `d` edges keep equal
parents and opposite sheets; `n` edges receive distinct parents.

The implementation author compiled the proof modules incrementally using
the pinned Lean 4.34.1, unchanged manifest, and separate writable project
build directory. The final `lake build CCO.SIR.Positive.Direct.CCO` passed
all 1005 jobs. Compiled source checkpoints are `e48fb3b` (signed consistency),
`843a8b0`/`3cc808c` (actual injective realization), and root-authored
`95853f3` (parent separation, retained as cherry-pick `258a80c`). The final
whole-package build, public-root closure and
official axiom audit belong to the B005 owner and exact remote/main CI.
This report is not a review or an assertion of batch acceptance.
