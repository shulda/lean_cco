# B046 — direct optional-coordinate potentials

Actual author: `/root/b046_orbital_cover/nine_colour_model/coordinate_potentials`.
Worktree `cco-b039`, branch `work/B046-coordinate-potentials`, based on accepted
main `6a3ed6e3a485b3218b5038b38494a7de1f821241`. Source pin and contracts unchanged.
Read the actual selected source in `sections/v27/06_legacy_finite_covers.tex`
and `formalization/orbital_cover_boundary/PROOF_NOTES.md`.

This contribution supplies the actual coordinate product and profile proofs
C16/C23/C24/C27, the direct constructive part of C19–C22 and the prescribed-
coordinate construction needed for C39. The independent actual
product source, homogeneity, SAP, triangle reconstruction and unary-prefix
source wrappers belong to the parent contribution. No overall completion
claim is made by this scoped report.

## Source-to-Lean map

- `Example.Potentials.signedGraph` keeps only specified edges carrying an
  actual optional sign. Unsigned `n` edges impose no phase constraint.
- `signed_cycle_readout` restricts original source `CycleHom` witnesses to
  genuine simple cycles in that signed subgraph. It reads the actual old
  points, including literal last-to-first wraparound.
- `optional_phase_labels` telescopes each such simple cycle, invokes the
  already proved repeated-vertex/two-edge-return cancellation in
  `SIR.Positive.Direct.SignedWalk.closed_parity_zero`, and constructs an
  actual potential separately in each signed component. This is C19/C21.
- `Example.Potentials.coordinate_blocks` uses the earlier actual
  `CycleConsistency.coordinate_labels`: an `n` edge within one equality
  component would close a genuine specified simple cycle with a shortest
  equality path. Finite components receive distinct natural block codes.
  This discharges C20 and the block-assignment part of C21.
- `coordinate_solution` combines those block labels with optional signed
  potentials. `Example.bitBool`, `boolBit`, their two inverse equations and
  `bitBool_add` identify the concrete `ZMod 2` phases with Boolean xor.
- `Example.semanticCCO_injective` instantiates the preceding construction
  independently in both actual coordinates of the nine-colour source.
  Distinct formal vertices receive distinct clone indices via their finite
  enumeration. Every recorded pair, including clone diversity `(e0,e0)`,
  is preserved. `semanticCCO` is the resulting actual semantic HOM CCO
  theorem in arbitrary finite vertex universes. This is C22.
- `coordinate_prescribed` retains literal prescribed endpoint phases after
  checking their equations only on signed edges. `coordinate_optional`
  chooses the unnamed or prescribed construction independently in each
  coordinate. `Example.realize_prescribed` simultaneously retains the
  optional original p/q prescriptions and produces an injective whole
  old-diagram realization. These are the concrete solver used by the two
  explicit successful prefix expansions in C39, not a safe-splitting axiom.

The inputs to the generic reader lemmas are actual source colour readout
identities. They are instantiated by the literal coordinate functions of
`Example.source`; the final semanticCCO theorem has no potential/CCO/Helly
provider premise. The prescribed solver's edge equations are exactly local
unary/edge legality, not an unproved global completion premise.

## Actual STRONG table and positive-word profiles

`Example.Products.coordTriangle` is the literal one-coordinate table:
e_i * e_j has output e_(i+j), e_i*n and n*e_i have output n, while n*n
permits all three colours. `coordinate_triple` reads any actual coordinate
triple. Conversely `coordTriangle_realized` explicitly constructs witnesses
for every permitted entry. `triangle_iff` combines the two independent
coordinate triples and assigns clone indices 0,1,2; it proves exactly the
actual `source.Triangle`, with three distinct real vertices. This is C16.

`Example.Profiles.product_boxes` proves factorization of the actual STRONG
product. `CoordProfile` has three singleton forms and Top, with its step
operation proved equal to that actual product table. `wordFactors` folds a
literal typed `PositiveWord source i j`, and `positive_profile_box` proves
by induction that its actual `PositiveWord.profile source` is precisely the
resulting Cartesian product. Every coordinate form is actually reachable
(`every_coordProfile_reachable`), and every word profile is nonempty. This
is C23, not merely an abstract recursive algebra.

`CoordProfile.helly` and `positive_profiles_helly` prove the pairwise-
intersection consistency check for arbitrary families (hence finite
families). These are C24; neither is used as a premise of semanticCCO.
`diagonal_not_box` proves the coarse diversity palette containing exactly
(e0,e0),(e1,e1) is not any Cartesian product. Therefore
`diagonal_not_positive_profile` separates it from every actual positive
STRONG word profile (C27).

The targeted `Example.Profiles` build passed 1214 jobs after the added
actual-table/profile proofs. Only the changed leaf modules were elaborated.

## Validation and provenance

Pinned local Lean 4.34.1, unchanged manifest and isolated local generated
outputs. Narrow builds passed: `Example.Potentials` (996 jobs), `Example.Bits`
(1142), `Example.CoordinatePotentials` (1176), `Example.CCO` (1178) and
`Example.Prescribed` (1178). Repeated counts include cached dependencies;
only changed targets were elaborated. No duplicate full-root, test or axiom
audit run was performed by this helper; parent assembly and exact-head/main
CI remain required.

The parent's stable `Example/Core.lean` is only an untracked, exact source
copy here for compilation and is excluded from this helper's commits.
Fifteen pre-existing private B043 dependency/report copies were preserved
before switching branches, with SHA256 inventory in
`runtime/B046-potentials-preserved-private-copies/manifest.json`. All original
branches and histories remain intact. No GitHub or coordination mutation was
performed by this helper.
