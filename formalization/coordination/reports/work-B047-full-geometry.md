# B047 — source STRONG saturation and FULL closure/EPP

Actual author: `/root`. Frozen source
`490c3f36d85db5a0b3ced0598e6c431825254ec5`; selected legacy finite-cover
proofs and pair_safe_split N01–N04/N08 were read before implementation.

| Contract | Actual declarations |
|---|---|
| C01–C03, D01/D02 | `CCO.PairSafeSplit.strong_exact_saturation_intersection`, with `product_meet_left` and `product_meet_right`: twice apply the accepted actual SAP+CCO STRONG exact distribution. Both multipliers and every domain are genuine nonempty STRONG exact menus; the evaluated common meet must be nonempty. All products use diversity triangles, including the empty restriction-family case. |
| C04, D03 | `Full.identity_closure_separation` uses the source's own real logical equality and actual increasing represented closures. No SAP or synthetic diversity identity is a premise. |
| C05 | `Full.kernel_closure_separation` constructs exact invariant stable powers above the WHOLE original K; `quotient_identity`, `pullback_comp`, `pullback_meet` prove actual surjective quotient pullback compatibility. No arbitrary old-to-quotient exact descent is assumed. |
| C15–C20, D06 | `Full.Sheet` is the actual represented deterministic rigid-arrow sheet. `allows_opposite_iff` retains nonrigid flexibility and possible logical identity; `typed_epp` derives full sheet primality from the accepted actual maximal-character mask primality. Its underlying proof invokes RAW nonempty saturation and original closure separation, never the new STRONG saturation theorem. `top_not_one_sheet` explicitly treats the zero-member family without selecting a nonexistent member. |
| C16/C21/C52 boundary | This file's theorem is FULL represented EPP and does not assert diversity/STRONG EPP by deleting Id. The latter has its independent original-SAP no-orthogonal-equivalences proof in the STRONG worker's modules. |

Names beginning `Full.` are relative to `CCO.PairSafeSplit.Full`.
The FULL lemmas use the actual `SourcePhase` on original reached kernels;
their displayed homogeneous/HOM-CCO source supplies all accepted algebra.
Actual finite-interval gate/phase construction is supplied separately before
the owner source theorem instantiates these lemmas. No final batch completion
or marked SAP is asserted by these scoped library results alone.

Pinned local Lean 4.34.1, bundled Lake and unchanged manifest:
`lake build CCO.PairSafeSplit.Full.EPP CCO.PairSafeSplit.Full.Closure CCO.PairSafeSplit.StrongSaturation`
passed 2,419 jobs with private incremental artifacts reused. This was a narrow
consumer build, not a duplicate whole-project test/audit pipeline. Public
exact-head/main CI, standard-three transitive audit and actual nonauthor
approval remain whole-batch requirements. No reviewer wrote/designed this code.
