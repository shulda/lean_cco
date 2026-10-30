# B038 atomic triangle-fullness implementation

Source pin: `490c3f36d85db5a0b3ced0598e6c431825254ec5`.
Source: `sections/triangle_fullness.tex`, `lem:cco-triangle-fullness`;
contract: `formalization/relational_completion/module.json`, C17–C29.
Actual new author: `/root/b038_atomic` (implementation and design).
Boundary implementation has its own author `/root/b038_atomic/boundaries`.

## Interfaces and scope

`CCO.RelationalCompletion.Atomic.Palette` has arbitrary `Sorts` and `Atom`
types, source/target typing and a typed converse involution. Neither type has
a finiteness instance or an ambient realization. `Diagram P n` stores exactly
complete vertex tags and optional diversity atoms; diagonal diversity is false
and converses and atom typing are explicit. `Model P` additionally has exactly
one diversity atom on each distinct pair. Its vertices are canonically `Fin n`.
This syntax represents all the complete atomic binary data in A04; there are
no unnamed extra predicates, ambient relations, or functional symbols.

`Embedding` is an actual injective vertex map preserving complete tags and
all atoms (including absent diagonal atoms). `Hom` has an arbitrary vertex
map and preserves tags and specified positive diversity atoms. Heredity is
closure under actual embeddings, hence includes isomorphism closure.
`AP` uses actual complete K-members and induced span embeddings, retaining
their equality on the base without imposing off-base disjointness.

`LocalAllowed K D` checks each individual unary tag and every specified pair
in K, including both endpoint tags. It imposes no constraints on unrecorded
pairs. `SemanticCCO K` explicitly takes this premise, then feasibility of
all specified simple cycles, and returns a whole positive homomorphism into
an actual K-member. It is not an ungated strengthening of A06.

## Source-to-Lean map

- D07: `Palette`, `Diagram`, `Model`, `Embedding`, `Hom` in `Palette.lean`.
- D08: `LocalAllowed`, `SimpleCycle`, `CycleHomInto`, `SemanticCCO` in `Class.lean`.
- D09: `FanRecorded`, `fanDiagram` in `FanDiagram.lean`; exactly all root-star
  and consecutive-path edges and their converses are recorded. Other input
  chords are absent from the partial fan.
- D10: `AP` in `Class.lean`, quantified over genuine complete induced spans.
- C17: `SmallSubmodels`, `pairIndex`, `tripleIndex`; the actual pair and
  triangle restrictions are put in K by the supplied small-submodel premise.
- C18: `fanRealized`, its three-vertex base branch (`k = 2`) uses the literal
  complete pullback triangle and identity vertex map. The auxiliary two-point
  base branch also supports boundary cases. `FanRealized` retains every unary
  tag, every consecutive edge and **every** old root-star chord.
- C19: `pairEmbeddingFromColour` constructs the actual complete-edge
  embedding; `Model.ne_of_colour_some` forces its endpoints distinct.
- C20: `fanRealized` calls actual `AP` on the current host, incoming actual
  triangle and shared complete edge. No strong amalgamation is assumed.
- C21: `point'` in `fanRealized` composes the entire old vertex map with the
  old-host embedding, appends the incoming triangle vertex, and separately
  proves `hsort'`, `hpath'` and `hstar'`. Thus **all** old stars survive,
  rather than merely retaining the most recent root chord.
- C22: `fanRealized` finite induction and `cycleHomInto_of_AP` closing-edge
  calculation; `fanDiagram_hom` packages the map as an actual `Hom` of the
  literal partial fan, including converse edges.
- C23: `cycleHomInto_of_AP` is quantified over an arbitrary specified simple
  cycle and returns its own actual K-host. It has no CCO premise.
- C24: `localAllowed_of_small` and the single `SemanticCCO` invocation in
  `triangleFullness`, after all cycle witnesses have been constructed.
- C25: `Hom.toEmbedding` injectivity proof uses each source distinct pair's
  positive diversity atom and false target diversity diagonal.
- C26: `Hom.toEmbedding.edge_eq` proves complete atom reflection: a distinct
  pair has its unique source atom, which is preserved; equality follows.
  Complete exclusive unary tags are preserved exactly; converses and logical
  equality/false diversity diagonals follow from the same embedding.
- C27: the final actual `Hereditary` application in `triangleFullness`.
- C28: `small_input_mem`, including size zero, one, two and three by the
  identity enumeration of the input itself.
- C29: `triangleFullness` in `Fullness.lean`.

## Independence and verification

The atomic branch imports neither the relational clone/collision branch nor
unaccepted B037 or old `AtomicSource` realization machinery. The main theorem
requires only the selected hereditary class, ordinary AP, locally allowed
semantic homomorphic CCO, and actual at-most-three-point induced membership.
It has no callback for triangle fullness, SAP, finite palette, homogeneity,
countable limit, injectivization, source realization or desired full-class
property. Nonadjacent fan vertices remain free to collide.

Narrow compilation uses the repository's Lean 4.34.1 and exact manifest. The
whole batch's final integration, exact-head CI/audit and independent review
remain the owner's separate obligations; this report does not certify them.
