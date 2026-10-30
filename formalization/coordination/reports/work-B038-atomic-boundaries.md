# B038 C33–C34 — actual finite-age boundary instances

Source: `490c3f36d85db5a0b3ced0598e6c431825254ec5`,
`sections/triangle_fullness.tex`; B038 module claims C33–C34 and notes N06.
Actual implementation actor: `/root/b038_atomic/boundaries`.
This actor implemented the boundary stream and is not an independent reviewer.

## C33: ordinary AP and actual legal triples without semantic CCO

`BoundariesAdapters.onePalette` has exactly one unary type and one symmetric
irreflexive diversity atom. The palette is an instance of the new unrestricted
Atomic interface, without using an ambient realization or finite-palette
premise of a general theorem.

`cliqueAge k` consists of exactly the finite complete models with at most k
vertices. `cliqueAge_hereditary` proves hereditary/isomorphism closure through
actual induced embeddings. `cliqueAge_AP` provides actual finite host models,
actual induced factor embeddings, and commutation on every base vertex.
The construction in `BoundariesFiniteAge.completeAge_AP` embeds the two sides
in the k-point clique, then uses an actual finite-carrier permutation aligning
the root images. It permits the off-base identifications of ordinary AP.

For the literal four-point input:

- `cliqueFour_small` gives all actual complete induced at-most-three-point
  members of `cliqueAge 3`, retaining every atomic edge.
- `cliqueFour_cycles` gives homomorphic realization of **every** specified
  Atomic simple cycle into the actual model `clique 3`. It uses the pinned
  Mathlib tricolouring of an arbitrary-length cycle, not bounded enumeration.
- `cliqueFour_no_hom` excludes a homomorphism to **every** member of that age,
  by complete-input inducedness and injective cardinality.
- `cliqueThree_not_semanticCCO` feeds the actual locally allowed complete
  input and those cycle maps into the SemanticCCO interface and derives the
  contradiction. Missing CCO is therefore an explicit substantive failure.
- `BoundariesFiniteAge.square_to_edge` is an actual C4-to-K2 map identifying
  opposite vertices, demonstrating why AP fans can legitimately collide.

## C34: K2 really has semantic CCO, but partial triples are insufficient

`BoundariesCycles.odd_closed_walk_has_odd_cycle` proves the actual unbounded
odd-closed-walk to odd-simple-cycle extraction. Strong induction on length
cuts a nonempty closed subwalk out of a non-path tail; one of that subwalk
and its complement is odd and strictly shorter. A path tail supplies the
actual simple cycle. This closes the Mathlib TODO needed here rather than
assuming bipartiteness from the cycle condition.

`no_odd_simple_cycle_isBipartite` then invokes the previously accepted
component-parity construction only after that extraction. The independently
proved `BoundariesTwoColour.cyclesFeasibleTwo_isBipartite` derives an actual
whole-graph K2 colouring from separate simple-cycle K2 colourings.

`BoundariesAdapters.cliqueTwo_semanticCCO` instantiates the **actual new
locally allowed Atomic SemanticCCO interface**, with no global-colouring
argument. A partial one-colour diagram gives its specified-edge graph;
`walkSimpleCycle` turns every graph-theoretic simple closed walk into the
literal Atomic cycle by its distinct `getVert` enumeration. Given cycle
realizations in arbitrary K2-age members, `cycleHom_two_bipartite` obtains
actual cycle two-colourings. The graph theorem yields one colouring of the
whole input, which is returned as an actual `Hom` into `clique 2`.
The local-allowedness premise is retained by the interface. In this one-type,
one-atom example it is automatically satisfied by singleton/edge witnesses.

`fiveCycleDiagram` is the literal partial C5 Atomic diagram:

- `fiveCycleDiagram_allowed` supplies actual allowed type and pair witnesses.
- `fiveCycleDiagram_triples` supplies an actual Hom of every three-point
  restriction (indeed every map `Fin 3 → Fin 5`, repetitions allowed) to the
  actual age member `clique 2`.
- `fiveCycleDiagram_no_hom` excludes a Hom of the whole partial C5 into any
  member of `cliqueAge 2`.
- `fiveCycleDiagram_incomplete` exhibits its unspecified 0–2 pair.
- `BoundariesTwoColour.fiveCycle_no_triangle` proves no displayed triangle.

The finite C5 facts are checked by Lean kernel reduction over this explicit
finite graph. These computations are not substituted for the unbounded
cycle-extraction or semantic-CCO proofs. No native-decide axiom is used.

## Validation and scope

Pinned Lean 4.34.1, existing pinned manifest; targeted imports only.
Narrow build:
`lake build CCO.RelationalCompletion.Atomic.BoundariesAdapters`
passed, 1274 jobs. The three graph modules also passed their earlier narrow
builds. There is no `sorry`, added axiom, external-provider binding,
triangle-fullness conclusion hypothesis, SAP hypothesis, or homogeneous
ambient target in these two boundary examples. Whole-batch build/audit and
independent exact-head review belong to the B038 integration owner.
