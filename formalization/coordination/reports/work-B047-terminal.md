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

## Actual successor and completed terminalisation

Read the actual selected `thm:safe-exact-split` and
`thm:finite-cover-elimination` proofs in the pinned finite-cover TeX.
The source notes' independent-SAP qualification is retained: the actual
marked SAP proof comes BEFORE all new-source STRONG readout.

`Terminal/Successor.lean`, namespace
`CCO.PairSafeSplit.Terminal.CurrentSource`, constructs `successor A P`
using the EXACT accepted B044 `SingleStep.successor A.base P`, and proves
its new SAP by the ACTUAL owner theorem
`SAP.unary_source_sap P A.base.cco (SingleStep.identification A.base P) A.sap`.
That owner theorem constructs infinite marked type fibres from old SAP,
actual gate geometry and the actual pulled-back global marking; this is
not an input callback or an assertion that an arbitrary seed is homogeneous.
`actualStep` keeps the same literal reduct/functor. `actual_progress`
chooses its own actual parity/maximal gate/character from EVERY CURRENT
finite relative interval and produces a genuine next SAP source with
strictly smaller potential.

`Terminal/Elimination.lean`, namespace `CCO.PairSafeSplit.Terminal`, exports:

- `safe_exact_split`: actual maximal-character P and its genuine successor,
  actual step, strict rank drop and all transported odd-arrow equations.
  The step contains the literal reasonable, reduct-surjective, precompact
  unary transition, and the new state intrinsically retains SAP/H/CCO.
- `finite_cover_elimination`: finite actual CURRENT-source history to a
  terminal source, bounded by initial sum of powers of three, and the
  SAME composite point/sort/atom reduct and forgetful functor.
- `initialSource` and `original_finite_cover_elimination`: original-source
  formulation with explicit old SAP/H/CCO/countability premises and actual
  terminal SAP, arbitrary-universe semantic CCO, FULL triangle realization,
  infinite relative classes for EVERY proper same-sort invariant cover,
  and the coherent precompact/reasonable/reduct-surjective unary functor.

Every history node is a `CurrentSource` carrying genuine SAP, not an
AP-only base whose endpoint is asserted SAP. No next-source, completion,
rank, Fraisse, safe-splitting or final-SAP provider remains in the principal
exports. The accepted AP-only terminal theorem is NOT applied to infer
new SAP; only its initial state constructor and generic finite-history
arithmetic/coherence support are reused. No later full-language, Ramsey,
EPPA or coherent EPPA theorem is used.

This closes this worker's C41–C51/D10–D11 source obligations, together
with the two independently requested C30–C32 type/avoidance support files.
The separate lifted STRONG algebra/phase-primality proofs are owned by
`/root/b047_strong_phase`, and whole-batch acceptance remains external.

## Scoped local verification

Pinned Lean4.34.1 and bundled Lake, unchanged manifest:

- `lake build CCO.PairSafeSplit.Terminal.Readout`: 2505 dependency jobs.
- `lake build CCO.PairSafeSplit.Terminal.OrbitCriterion`: 1336 jobs.
- `lake build CCO.PairSafeSplit.Terminal.TypeReflection`: 1439 jobs.
- `lake build CCO.PairSafeSplit.Terminal.Elimination`: 2519 jobs; all final
  successor and principal original-source statements compiled.

These are narrow owner compiles, not fresh-source counts or a full public
CI/audit certificate. No whole-root build, broad test/audit suite, reviewer
implementation or remote publication is performed by this worker.


## C41 selected-original-parity repair

The repaired `Full.ParityGateData.phase` retains its literal original
maximal odd arrow. `Readout.original_even`, `original_odd` and
`original_odd_walk` apply the proved original Y/O inclusions to the SAME
`SingleStep.identification` and its actual global marking. Thus every
original even pair has equal bits and every original odd pair has opposite
bits; this is stronger source linkage than a generic transported-arrow
statement alone.

`Terminal.SelectedStep` stores the selected original sort, anchor, orbital,
concrete parity gate and equality to its exact successor. Its actual step,
rank drop and all original parity equations are DERIVED. `selected_progress`
selects it from the current residual interval using visible current SAP.
`finite_cover_elimination_selected` and
`original_selected_finite_cover_elimination` iterate only these selected
steps and retain that metadata at every stage. The old safe-split and
elimination theorem signatures are compatibility wrappers through the SAME
selected construction, its actual history and its composite reduct/functor.
No arbitrary phase selector is used by the principal terminal proof.

The terminal author changed only `Terminal/Readout.lean` and
`Terminal/Elimination.lean` at native `f23aa9c`; the narrow Elimination target
passed 2,521 jobs after Readout passed 2,507 jobs. The owner supplies the
original root/phase linkage and the final selected source assembly. This
is author work, not independent review; the final exact-head CI and true
review approval remain separate.
