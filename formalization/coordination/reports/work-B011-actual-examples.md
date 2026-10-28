# B011 actual coordinate and Cartesian phase examples

Scope: real_closure C17–C18 and C32–C34. All allocated actual-source
providers and consumers are complete; no external homogeneity, CCO,
full-group, packet, closure or nonexactness provider remains as an input.
The code is under `CCO/RealClosure/Bounds/Examples/` only. This helper
has not edited `CCO.lean`, the contract, the manifest or accepted APIs.
The batch owner must import every public module and perform its one final
whole-project build and official axiom audit.

Actual mathematical source proofs were read in:

- `sections/real_hull/06_minimal_infinite_directions_acl.tex`, coordinate
  sharpness `ex:rh-acl-polynomial-sharp`, blob
  `4c01beca2f60acfa2d942714525173889bc5804f`.
- `sections/real_hull/07_sap_mi_intersection_geometry.tex`, actual Cartesian
  phase `ex:two-coordinate` and `rem:phase-thin-not-exact`, blob
  `7d681c9087c1d7f41ea65a834158daf456ee5fd2`.

Both current source hashes were checked literally against `module.json`.
The source pin is unchanged:
`490c3f36d85db5a0b3ced0598e6c431825254ec5`.

## Genuine simple-cycle completion

`CycleConsistency.lean` is a generic typed source theorem. Given actual
`CycleHom` for every specified `SimpleCycle`, a coordinate reader whose
actual colours read equality yields natural-number labels satisfying ALL
specified equalities AND inequalities. A contradictory inequality is joined
to a shortest equality path, producing a literal specified simple cycle.
The phase reader similarly produces a Boolean potential with every actual
edge gain. It unrolls actual cycle homomorphisms, uses the accepted generic
signed-walk decomposition to prove all closed gains vanish, and integrates
one potential per connected component. No independent coherence premise,
finite snapshot certificate, SAP or new axiom is used.

## Coordinate family: C17–C18

`Coordinate.lean` constructs the literal carrier `I → Nat`, the nonempty
finite difference-support sets as diversity atoms, and actual optional
colour equality. `Aut I` is the subgroup of ALL colour-preserving point
permutations. Finite coordinate maps extend via the accepted
`exists_perm_of_kernel` lemma to actual coordinate permutations, proving
`HomogeneousSource`.

`CoordinateAut.lean` proves a group isomorphism between the product of all
coordinate permutation groups and the FULL actual automorphism group.
`CoordinateCCO.lean` instantiates the actual simple-cycle coordinate readers
in every coordinate. It proves `SemanticCCO` for an arbitrary universe of
formal vertices, and actual age AP follows from the proved homogeneity.
This is a proof about the infinite source, not a finite control table.

`CoordinateLattice.lean` proves the order isomorphism
`Finset I ≃o ColourEq (source I) ()`. Its critical step constructs two
edges of the SAME original difference support using a fresh third natural
coordinate value, forcing every singleton support in an invariant
equivalence. All other points are connected by actual single-coordinate
changes. Every nonempty coordinate-change class contains an explicit copy
of Nat.

`CoordinateDirections.lean` uses the batch's SAME shared `FiniteClasses`,
`finitePacket`, `IsDirection` and `Direction` definitions. It proves:

- finite-class equivalence iff actual equality, hence `F = Id`;
- actual minimal infinite directions correspond bijectively to `I`;
- `directionCount = Nat.card I`;
- the number of diversity atoms is `2^(Nat.card I)-1`.

`CoordinateClosure.lean` reads the finite sets of coordinate values in an
actual finite base. A tuple in their grid is fixed by EVERY actual full
stabilizer automorphism. Outside the grid, explicit fresh swaps fixing the
ENTIRE base embed Nat into the actual stabilizer orbit. Thus the batch's
actual `Acl` and `Dcl` both equal that literal grid. For the actual n-point
diagonal base the grid is explicitly bijective with `I → Fin n`, giving
closure cardinality `n^(Nat.card I)`, including n=0 and n=1.

`CoordinateNonSAP.lean` gives a literal off-base corner fixed by the full
stabilizer of two actual anchors. The accepted actual age-SAP duplication
provider would make its orbit infinite, contradicting fixedness. No
classification theorem or assumed SAP orbit claim replaces that provider.
`CoordinateConsumer.coordinate_sharpness_source r (2 ≤ r)` assembles the
actual infinite Nat^r source, all hypotheses, packet and direction counts,
sharp closures and failure of SAP.

## Cartesian phase source: C32–C34

`PhaseSource.lean` constructs the literal infinite carrier
`Nat × Nat × Bool`. Its colour pattern is the two coordinate-equality
flags and the Boolean phase difference. The omitted `(true,true,false)`
pattern is actual equality; all seven diversity atoms are realized.
`Aut` again means ALL colour-preserving point permutations. Every actual
automorphism is proved to consist of two permutations of Nat and one common
phase translation; finite partial maps extend by precisely such a motion.
`PhaseCCO.lean` instantiates both genuine coordinate-completion readers and
the gain-potential reader, proving arbitrary-universe semantic CCO. Actual
age AP and homogeneity are proved, not assumed.

`PhasePackets.lean` proves that the literal same-row/same-column relation
has classes bijective with Bool. Any original equivalence relating points
with a changed infinite coordinate has a class containing Nat, using actual
coordinate motions fixing the first endpoint. Thus the batch's greatest
finite packet is EXACTLY the literal two-point packet, of cardinality two.
Algebraicity is packet-saturated by an explicit finite image of
`orbitOver x × Bool`, with no model-theoretic transitivity input.

`PhaseCorner.lean` uses the two ACTUAL source colours from
`origin=(0,0,false)` to `a=(0,1,false)` and `b=(1,0,false)`. These colours
uniquely determine the origin. It is therefore in actual real dcl and acl
but outside the finite packets of both anchors. The literal square words
for the two colours represent the row/phase and column/phase equivalences,
INCLUDING actual equality endpoints. Their generated Gamma equivalences
are proved equal to those word profiles, their meet is actual identity,
and their indicated classes intersect in exactly `{origin}`. The thin
flip also directly contradicts actual SAP point gluing; the source remains
AP and semantic CCO.

`PhaseExact.lean` proves, by induction on the ACTUAL typed RAW word, that
every endpoint phase difference is the sum of its letters. The empty word
has zero gain and identity letters are retained correctly. Any nonempty
restriction list therefore has a fixed endpoint phase. The empty list is
handled separately as Top. Proper finite packet, phase-forgetting row,
and phase-forgetting column equivalences each contain both equality and
the thin flip, so NONE is FULL RAW exact. No general exactness of Gamma,
no equality `Kfin = F`, no SAP or quotient-source claim is made.

`PhaseConsumer.phase_counterexample_source` assembles the actual infinite
source, seven atoms, all source hypotheses, true packet and saturation,
explicit corner, exact square-word kernels, canonical singleton and all
three nonexactness results.

## Provenance and validation

Actual authors:

- `/root/b010_canonical/coordinate_examples`: coordinate family and actual
  lattice/directions/closures, phase packet/corner/nonexact consumers.
- `/root/b010_canonical/coordinate_examples/cycle_consistency`: generic
  actual cycle consistency and, on an explicitly authorized same-actor
  extension, actual phase source/full-group/homogeneity/AP/CCO.

The implementation uses accepted B001/B008/B010 APIs and the SAME in-batch
Packet/Directions/Algebraicity interfaces. It imports no unaccepted B013 or
B019 theorem. No reviewer participated in implementation design.

Final targeted module builds succeeded with the pinned Lean 4.34.1 runtime:

- `CoordinateConsumer`: 2285 jobs, all actual coordinate claims closed.
- `PhaseConsumer`: 2283 jobs, all actual phase claims closed.
- Generic cycle consistency: 995 jobs in the helper worktree.
- Actual phase source and semantic CCO: 1039 jobs in the helper worktree.

There are 15 new public example modules. No helper whole-project build or
axiom audit was repeated; the batch owner retains those final gates.

Own compiled source commits are `832b509`, `dc05e78`, `b5dce18`,
`4f6fcf6`, `c3b3847`. The generic helper is `71032db` and its actual phase
source extension is `f3de7bd`. Shared Packet `4c4bccd`, Directions
`e70f38f` and Algebraicity `2acc86b` appear in the helper history only to
compile the same in-batch interfaces; the owner already has those files.
The final report commit changes this prose report only.
