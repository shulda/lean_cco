# B006 source-complete local validation

The complete proof source is frozen at
`7d87c2996ba269329de438baa6cb6d855af9dc63`, based on accepted main
`647b1b76cc075dce477974b74293eb9370ff9b5d`. Later commits only document
the source map and these checks. The live claim remains governed by
`coordination:formalization/coordination/STATE.json`; this report does not
declare acceptance or alter public queue state.

All parity/Hasse C01–C14 and original SIR C15–C19 are implemented against
the actual source objects. The source pin remains
`490c3f36d85db5a0b3ced0598e6c431825254ec5`. Read source blob hashes:

- `sections/sparse_labelled_graphs.tex`: `c7db0b7169dd8ff4dcd5642469ac8fa42c2ef530`.
- `sections/finite_relative_parity_exact_closure.tex`: `9f6983f96bae28d06466fcbf23f15e20a55f2686`.
- `sections/stationary_independence_scope.tex`: `4b01269755936a728965e5df5dfb4e1e91e02cd3`.

The exact theorem/hypothesis map is `../submissions/B006.md`; the detailed
finite probability construction is `work-B006-sparse.md`. The actual
finite sparse labelled graph constructor proves its concentration,
cycle-expectation, simultaneous-event and deletion inputs. The final
`full_relative_hasse`, `finite_relative_power_two`, and SIR
`fullRelativeHasseProvider_of_source` discharge every graph/parity/Hasse
provider. Honest intermediate conditional interfaces remain available.

The final Hasse statements concern all original invariant equivalences
and genuine relative quotient classes. They assume homogeneous original
source, finite palette and CCO on finite ordinal diagrams. No SAP,
countability, exact-endpoint, RAW Helly or supplied sparse-graph premise
is added. The SIR obstruction requires a proper actual invariant global
finite quotient; local relative finiteness alone is not used to assert it.
Meaningful consumers include the actual index-three full-cover exclusion,
connected triangle-free chromatic graph and invariant finite quotient map.

Local pinned Lean 4.34.1 validation completed once for the assembled proof
tree after targeted development builds:

- `lake --rehash build`: passed, 2353 jobs.
- `tools/verify_project_cache.py --require-complete`: all 350 current source
  modules and generated parts consistent, both before and after audit.
- Official `axiom-audit --root CCO --allow propext,Classical.choice,Quot.sound`:
  4251 declarations checked; all within the allowlist.
- All 33 new modules are directly imported by `CCO.lean`.
- The designated nonauthor reviewer read the complete proof source and
  submission map with no blocker; no duplicate whole build was requested.

Actual implementers are `root`, `/root/b006_parity`, `/root/b006_sir`,
`/root/b006_parity/sparse_graphs`, and
`/root/b006_parity/sparse_graphs/numeric_bounds`, with individual scopes
preserved in the submission map and commit history. Review-only roles
authored no implementation. Mathematical contracts, toolchain, manifest,
source pin, accepted theorem definitions and public queue policy are unchanged.

Pending acceptance gates: publication of the final documentation head,
exact-head remote CI/audit, recorded nonauthor approval bound to that head
and tree, and resulting-main CI under the single integration lock.
