# B014 C30–C31: actual infinite twin-cell source

Author: `/root/b014_normalization/twin_example`. Base main:
`8b165711491be83a7043dd4d40f818aa17ebcc05`.
Source remains `490c3f36d85db5a0b3ced0598e6c431825254ec5`;
`sections/finite_packets.tex` has the contracted blob
`dd3e608f03e7c5b1b1854a45de462859f8355143`.
Read its actual `ex:thin-not-exact-free` proof and preparation N08.

Six new public modules, 845 lines, namespace
`CCO.FinitePackets.Normalization.Examples.Twin`:

- `TwinSource`: literal `Nat × Nat × Bool`, exactly four diversity colours
  `twin/row/column/apart`. Only twin sees the bit. `Aut` is the FULL group
  of colour-preserving permutations. `aut_representation` and
  `motion_bijective` identify it with independent permutations of both
  entire Nat coordinates and arbitrary independent cellwise Boolean
  shifts. Actual `finite_extension`, `homogeneous`, `ageAP` and
  `infinite_twin_source` are discharged.
- `TwinCCO`: `semanticCCO` in arbitrary finite-diagram universes. Accepted
  actual specified-cycle `coordinate_labels` solves both coordinate
  systems. A separate `twinGraph` keeps ONLY actual t-edges. Each genuine
  simple graph cycle is converted to a literal original specified
  `SimpleCycle`; its actual homomorphism gives telescoping Boolean
  parity. Accepted signed-walk cancellation and potential construction
  produce a bit labelling. No gain condition is imposed on r/c/b edges,
  and no extra cycle-consistency provider is assumed.
- `TwinPackets`: actual invariant `packetEq`, `rowEq`, `columnEq`;
  `packetClassEquiv : F[x] ≃ Bool` and exact cardinal two. Every finite
  original invariant equivalence is below this packet, by explicit
  original motions injecting Nat into any class containing a changed
  coordinate. Thus `finitePacket_eq` identifies the literal accepted
  greatest finite packet with this two-point cell relation.
- `TwinExact`: actual `row_square` and `column_square` RAW double-word
  profiles. Their nonempty exact meet is `packet_exact`;
  `packet_nonidentity` uses the two real points in a cell.
  `packet_iff_eq_or_twin` identifies F=Id union t, `twin_iff_flip`,
  `twin_thin`, `twin_square_identity` prove its sole diversity atom thin
  with actual square Id. `all_packet_atoms_thin` supplies the square
  regularizer's thin branch. `row_minimal_infinite` proves the row
  equivalence is a literal minimal infinite cut, including actual
  finiteness before class counts. `row_inf_column` and
  `row_inf_finitePacket` give E meet c²=F. For EVERY real x and EVERY
  distinct target row, `conditionalFibreEquiv` identifies the actual
  conditional c-fibre with Bool; `conditional_fibre_card` is exactly 2.
- `TwinQuotient`: `packetQuotientEquiv` is an equivalence from the literal
  `Quotient packetEq.val` to Nat² and is equivariant for the actual
  quotient action of the original full Aut. `cell_orbital_iff` identifies
  ALL actual induced pair orbits on Nat², by genuine original motions.
  `actualCellAtomEquiv` is a bijection between the actual
  `QuotientPalette.DiversityAtom` relation type and the three non-twin
  old colours. `quotient_diversity_card` is 3 and
  `quotient_palette_strictly_decreases` compares it to the original 4.
  This uses only actual group-action quotient algebra, with no quotient
  homogeneity/CCO inheritance premise.
- `TwinConsumer`: `triangle_defined` instantiates the accepted actual
  AP+CCO triangle-fullness theorem. `thin_not_exact_free_source` bundles
  the literal H/AP/arbitrary-universe semantic CCO, four-colour palette,
  greatest two-point packet, thin atoms, nonidentity RAW-exact packet,
  minimal row cut, all conditional two-point fibres and true quotient
  palette drop 4→3. No source/provider assertion remains open.

Local final helper target:
`lake build CCO.FinitePackets.Normalization.Examples.TwinConsumer`:
**2290 jobs PASS**, Lean 4.34.1/Lake 5, exact committed manifest.
Only targeted incremental builds were performed; the B014 owner performs
one complete package build, official axiom audit and full artifact/current
source guards after integration. No mathematical source, contract, accepted
API, manifest or toolchain was changed. The package owner adds all six
public imports to CCO.lean. This is implementation evidence, not independent
review or final batch submission.
