# B044 identity-fold cycle witnesses

Actual contributor: `/root/b044_ap_character/identity_completion/quotient_cycles`.
This is implementation provenance, not an independent review or batch acceptance.
Base: accepted release main `e77b672fd17704e92d39786cbb8818adb36a9fcb`.
Source pin remains `490c3f36d85db5a0b3ced0598e6c431825254ec5`.

## Scope and actual theorem

`CCO/APCharacter/Completion/FoldCycles.lean` proves the genuine C25-C27 cycle
obligation for the literal `foldDiagram` constructed by the sibling helper.
The final declaration is `CCO.APCharacter.Completion.fold_cycleHom`.
It retains arbitrary original sort/carrier/atom universes, the old finite
`PartialDiagram`, an old `DiagramHom`, distinct nonadjacent selected vertices
with equal original sort, and original identity path bounds in both
orientations. Both bounds are supplied by the same selected all-simple-path
identity output (`identity_bounds_of_graph` in the receiving completion).
No SAP, triangle-definedness, marked realization or new homogeneity premise
occurs. This theorem has no opaque cycle-decomposition or quotient-CCO input.

The proof selects literal old endpoints for each new cycle edge using
`pushDiagram_lift`. Away from the one merged fibre those endpoints are unique.
A cycle avoiding that fibre uses the old homomorphism directly. A cycle
through it is rotated so the merged vertex is position zero. Its edge lifts
form a literal old line of length equal to the cycle length: the whole prefix
is injective, every consecutive pair is an actual specified old edge, and
only its first and last old vertices can coincide. Coincident ends use the
old homomorphism. Distinct ends make the entire old line injective and force
its endpoints to be the selected pair in one orientation. The corresponding
original identity bound gives an actual represented path with equal real
endpoints. The accepted finite-line readout and explicit sorting transports
turn it into a `CycleHom` for the SAME new cycle, including its closing edge.
Cycle rotation is undone by the accepted literal reindexing equivalence.
No equality-labelled diversity edge is ever introduced.

Only the elementary finite-line and cycle-index combinatorics from the
accepted StrongExact tree are reused; none of their SAP-dependent profile
or completion theorems is applied. Old source atom names are compared through
actual tagged-colour equalities, not by replacing them with quotient atoms.

## Verification and preservation

The narrow target `lake --rehash build +CCO.APCharacter.Completion.FoldCycles`
passed 1102 Lake jobs; the final changed module compiled in 2.2 seconds.
Only targeted compilation was run, no broad CCO build, tests or axiom-audit
pipeline. The batch owner and exact-head/resulting-main CI retain their normal
final verification gates. All imported helper source commits and old B043
branches/history are preserved in the stable physical `cco-b039` slot.
