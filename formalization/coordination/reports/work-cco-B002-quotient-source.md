# B002 — actual C14–C19 source-provider discharge

28 October 2026. Source proof checkpoint:
`569caf5384d423f6215c670332fef16c8291c0ec` on local
`work/raw-quotient-source`, a leaf after combined checkpoint `b7e7b054`.
This is **IN_PROGRESS** package work, not a batch submission or acceptance.
The original source pin, contracts, toolchain and manifest are unchanged.

## Actual signatures and providers

All quotient maps below are actual equivariant maps from the original
real sort carriers. Equations identifying their kernels with the given
full-exact equivalences are source data, not arbitrary quotient-colour
representation providers. No equivariant section, quotient homogeneity or
lift coherent across quotient sorts is assumed.

| Claim | Discharged source theorem / precise scope |
|---|---|
| C14 | `ActualQuotientSource.exact_actual_orbit_pullback_of_CCO` constructs a nonempty exact presentation of the pullback of every actual quotient pair orbital from the two actual exact kernels, original homogeneity and original semantic CCO. The original pair presentation is supplied by `ActualOrbitalExact.actual_original_orbital_exact`; the old arbitrary `A/hA` and Helly providers are discharged. Existing `Saturation`/`QuotientDescent` prove the actual kernel-saturation identity, invariance and descent. |
| C15 | `FineColoursSource.fine_colour_reconstruction_of_CCO` proves the finite exact equivalence meet/saturation equation. Reflexivity supplies the genuinely nonempty resulting meet required by C10. `actual_fine_pair_orbit_of_CCO` states the actual quotient-colour reconstruction for quotient maps whose common finer kernel is precisely that meet. Arbitrary tuples of quotient classes are not asserted realizable. Original `none` is true identity and is explicitly represented by `optional_original_atom_exact`. |
| C16 | `ActualQuotientSource.exact_equivalence_join_of_CCO` constructs the nonempty exact join, with equivalence and full least-upper-bound clauses. Existing `ActualMixedMaps.actual_mixed_orbit_reduction_of_join` and `actual_mixed_partial_maps_of_join` already discharge the actual mixed-orbit and finite-domain clauses; their common partial quotient map covers both complete projected domains. |
| C17 | `ActualNestedMaps.actual_nested_orbit_reduction_of_homogeneous` derives the actual mixed-orbit reduction from commuting actual equivariant quotient projections. Kernel nesting follows from commutativity; same-sort source algebra proves the saturation equality. `actual_nested_partial_maps_of_homogeneous` then discharges the old `hReduce` provider while retaining full projected-domain coverage and pointwise agreement. This algebra needs original homogeneity, not CCO/exactness. |
| C18 | `ActualQuotientSource.actual_orbital_private_paths_of_CCO` constructs the exact actual orbital presentation and provides ALL private word-walk witnesses for EVERY pair of chosen real representatives of any pair in that orbital. Multiple word occurrences stay independent in `PrivatePaths`. The later formal quotient-cycle expansion/classification is a separate C26 obligation. |
| C19 | `ActualQuotientSource.exact_actual_request_of_CCO` constructs the nonempty full-exact actual real-to-quotient request using the actual exact kernel and the proved source C13. Existing `QuotientRequests` proves actual request equality and representative independence; `Saturation.right_request_saturated` proves right kernel saturation. |

Only original `HomogeneousSource S G` and `SemanticCCO S` discharge the
Helly/distribution inputs. The exact-kernel hypotheses remain explicit
because the contract is about chosen full-exact quotient sorts. No stronger
SAP, fresh-point axiom or actual group-orbital hypothesis has been hidden.

## Verification

All three new public modules are imported in root `CCO.lean`.
Pinned Lean 4.34.1 complete build: **938 jobs, success**. Each new module
also compiled independently with the pinned compiler. Fresh root-import
signature checks confirm all three principal source exports are present.
Transitive module-origin `Lean.collectAxioms` audit: **1,491 CCO declarations**,
including private/generated names; only `propext`, `Classical.choice`,
`Quot.sound`. No placeholder or new mathematical axiom was introduced.

A copied build directory initially left a stale root `CCO.olean` despite a
successful build trace. This was detected by checking the new source
signatures and the unchanged declaration count. Removing ONLY generated root
outputs and rebuilding materialized the correct root; the signature checks
and 1,491-declaration audit above were then rerun successfully. The source
files and pinned build configuration were not altered for that repair.
Cross-worktree project caches therefore need artifact/materialization checks,
not just a successful trace.

Remote exact-head CI and genuinely non-author review remain required.
C06's explicit whole-cycle/two-private-path classification and C24–C28
actual quotient-age triangle/AP/cycle/CCO obligations remain open; the
separate C20–C23 lifting implementation is being combined by its owner.
