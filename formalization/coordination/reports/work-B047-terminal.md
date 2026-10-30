# B047 — SAP current-source terminalisation contribution

Actual author: `/root/b047_terminal`. Source pin:
`490c3f36d85db5a0b3ced0598e6c431825254ec5`. Work starts at the actual
accepted main `bfbf8cf83d590d8d13499ab0e33aa8ea6445eb97`, following the
effective B047 claim379. Old B044 branches are preserved. Seven untracked
private compile copies were archived with exact SHA256 hashes before
switching the physical worktree to `work/B047-sap-terminal`.

Read the actual B047 contract, complete proof notes N01–N08, and the
accepted B044 state, canonical source, rank and coherent reduct proofs.
No accepted API, mathematical source, toolchain, manifest or external
provider/cache policy is changed.

## Implemented support and actual signatures

`CCO/PairSafeSplit/Terminal/Current.lean` is under namespace
`CCO.PairSafeSplit.Terminal`. Its `CurrentSource` keeps the accepted B044
base source AND genuine real `AgeSAP` as separate data; an AP-only field
is never renamed SAP. The nested `CurrentSource` namespace supplies:

- `semanticCCO`: actual finite reindexing transfers the base CCO property
  to every formal-vertex universe.
- `full_triangle_age`: an actual homogeneous HOM-CCO complete source
  realizes every complete small-type-legal network. Singleton/pair and
  empty cases use real admissibility, not triangle vacuity.
- `actual_pair_orbital` and `named_sort_transitive`: whole current source
  homogeneity, rather than childwise or arbitrary seed homogeneity.
- `terminal_interval_infinite` and `terminal_cover_infinite`: absence of
  ANY proper finite-relative interval implies infinity in the full actual
  invariant lattice, not a chosen exact sublattice.
- `ActualStep`, `baseHistory`, `historyReduct`, `historyTransition` and
  `history_forget_eq`: the same actual point/sort/atom reduct and its
  reasonable, reduct-surjective, precompact finite-age functor compose
  along the identical finite history.
- `history_length_bound` and `no_infinite_safe_splits`: strict integer
  descent bounds actual step count, including the zero-step case.

`Terminal/Readout.lean` is under `CCO.PairSafeSplit.Terminal.Readout`.
Every statement uses the EXACT B044 `SingleStep.identification B P`:
`marking_arrow`, `transported_odd_orientation`, `gate_constant`,
`active_children_card`, `active_child_nonempty`, `inactive_children_card`,
`whole_expanded_orbitals`, `lost_original_colour` and
`actual_potential_drop`. Thus the two actual inhabited children and lost
old colour discharge the genuine whole-expanded integer rank hypotheses.
No rank, orbit-recognition or colour-loss provider is supplied.

Two additional files are generic support requested by the actual SAP
implementation owner, and deliberately import ONLY accepted dependencies:

- `Terminal/OrbitCriterion.lean` is under `CCO.PairSafeSplit.SAP`.
  `ageSAP_of_many_same_type T H many` converts arbitrary finite injective
  complete-type witness families into actual pointwise stabilizer orbits.
  A proposed finite orbit cannot contain card+1 distinct witnesses.
  Accepted simultaneous avoidance then proves whole relational age SAP.
  This helper assumes no CCO, countability, SAP or orbit-infinitude axiom;
  its actual multiplicity hypothesis must be constructed separately.
- `Terminal/TypeReflection.lean` is also under `CCO.PairSafeSplit.SAP`.
  `oldBase I B` is the actual oldEquiv-image finite base.
  `sameType_of_old I B x y hChild hOld` reflects the complete old type
  to the complete new type at fixed child tags. The convenience
  `sameTypeOver_of_old_and_mark` derives those tags from the actual bit.
  Logical equality and both pair orientations remain in the proof.
  This is a direct statement on the SAME actual canonical source; no
  second chart embedding or arbitrary homogeneous seed is introduced.

## Current completion boundary

The four modules compile. The genuinely actual marked SAP theorem is
being proved by `/root/b047_pair_safe_split` from old SAP and actual
infinite old-type/gate intersections. Once its exact
`SAP.unary_source_sap` instance is available for the canonical B044
identification, this contribution will instantiate the actual successor
at EVERY current source and finish the principal finite terminalisation.
No generic progress callback currently certifies that unclosed source
obligation, and this report does not assert batch completion or acceptance.

## Scoped local verification

Pinned Lean4.34.1 and bundled Lake, unchanged manifest:

- `lake build CCO.PairSafeSplit.Terminal.Readout`: 2505 dependency jobs.
- `lake build CCO.PairSafeSplit.Terminal.OrbitCriterion`: 1336 jobs.
- `lake build CCO.PairSafeSplit.Terminal.TypeReflection`: 1439 jobs.

These are narrow owner compiles, not fresh-source counts or a full public
CI/audit certificate. No whole-root build, broad test/audit suite, reviewer
implementation or remote publication is performed by this worker.
