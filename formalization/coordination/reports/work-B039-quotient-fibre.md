# B039: actual named quotient fibres, AFF and both necessity clauses

Actual contributor: `/root/b039_fresh/quotient`. This is implementation work,
not independent review. Source pin is
`490c3f36d85db5a0b3ced0598e6c431825254ec5`; no source TeX, accepted API,
toolchain or manifest was changed. The only mathematical external import is
accepted B010's `CCO.AclOwners.Avoidance` (actual finite-action avoidance).

Read source: `sections/unary_fresh_frame_sap.tex` and the B039 source contract,
`formalization/unary_fresh_frames/module.json` / `PROOF_NOTES.md`, especially
N04–N08. The homogeneous hereditary criterion is implemented by the sibling
SAP stream and is actually consumed in `Quotient/SAPNecessity.lean`.

## Mathematical source map

Names below are in `CCO.UnaryFreshFrames.Structure` unless prefixed
`Quotient`, which means `CCO.UnaryFreshFrames.Quotient`.

| Claims | Actual implementation |
| --- | --- |
| C18 | `NamedFunctions`, `namedValues_eq_closureAt`, `namedFunctions_finite`; `Quotient.equivariant_ext` and `finite_semantic_functions` prove evaluation at one actual real point determines the complete semantic function. Output sort is recovered by `termFunction_output`; no finite syntactic term or finite language assumption. |
| C19 | `Quotient.fibre_transitive`: a genuine element taking one real point to another in the same actual projection fibre fixes the quotient point. |
| C20 | `named_orbit_eq_fibreValues`, `named_full_orbit_eq_fibreValues`; BOTH actual subgroup and full-Aut quotient-point stabilizer orbits equal the same actual term-image set. `fibreKernelEquivValues` bijects kernel classes inside that actual fibre with the actual image. No group-index interpretation. |
| C21 | `Quotient.arbitraryFibreValuesEquiv` restricts an actual transitivity motion to a bijection of any two fibre-image sets, for finite AND infinite indices. |
| C22–C24 | `Quotient.common_fibre_avoidance` applies B010 ONCE to the finite set of all distinct unforced term values. `named_fibre_avoidance` instantiates this with actual typed named terms and literal named forced factors. Forced values remain fixed, including forbidden forced values. |
| C25 | `named_fibre_avoidance` proves `closureAt x ∩ Z = closureAt b ∩ Z` exactly. Every closure point is an actual named term value; unforced values avoid Z; actual named factors put forced values in the base closure. The actual named projection proves the reverse inclusion. |
| C26 | The identity term's semantic function is the injective source-carrier inclusion. Strictness of the actual projection kernel makes it unforced, so the SAME representative itself avoids Z. |
| C27 | `NamedQuotientSystem.finite_sequential_choices` and `finite_sequential_avoidance` construct arbitrarily long finite sequences across different real and quotient sorts, pairwise distinct representatives and actual projection equalities. Each new unforced value avoids Z AND every earlier representative's entire singleton closure. Forced values may recur. |
| C28–C33 | `NamedQuotientSystem` records actual named projections, their surjectivity and strict actual kernels, and representations of every nonreal point. `quotient_system_fresh_frame` uses Finset induction over ALL A points, taking an actual real A point itself or a newly constructed quotient representative avoiding B and all previous generators. Unary singleton additivity proves AFF, including orphan hidden points and empty A. No homogeneity, real-base orbit, countability, finite language or SAP premise enters this construction. |
| C37 | `kernel_clauses_of_ageSAP` derives full-Aut orbit infinitude and singleton acl=closure from actual `AgeSAP`, `Homogeneous` and local finiteness, using the expanded sibling criterion. There is no remaining closure oracle in this source instance. |
| C38 | `forced_value_mem_dcl` uses named projection and term equivariance under EVERY full automorphism fixing the quotient point, before any named factor assumption. |
| C39–C40 | `exists_named_term_of_closure` gives an actual well-sorted syntactic term from singleton closure membership. `named_factor_of_one_value` uses actual subgroup transitivity to globalize ONE equality to the literal named factor. |
| C41 | `Quotient.exists_other_fibre_value` transports a genuine kernel-noncontainment witness to every nonempty fibre; `exists_stabilizer_moves` gives an actual subgroup motion. |
| C42 | `finite_fibre_value_mem_acl` uses FULL-Aut invariance of the finite actual fibre image, without equating the subgroup and full automorphism group. The explicit full-orbit equality is also proved. |
| C43 | `nonforced_value_not_mem_closure` obtains an actual subgroup base-fixing move; every named closure value is fixed by that move. Thus the term value is off named closure. |
| C44 | `infiniteUnforcedIndex_of_acl` contradicts actual full-Aut acl=closure using C42/C43. `kernel_clauses_of_ageSAP` discharges the acl premise from actual SAP and derives BOTH clauses without assuming either. |
| C47 | `missing_named_factor_off_closure`: actual forced fibre value is full-Aut definable, but membership in named closure would yield a real named term and global factor, contradicting the supplied missing-factor failure. No SAP premise. |
| C48 | `finite_proper_index_off_closure`: finite actual fibre image gives full-Aut algebraicity, while subgroup transitivity witnesses off-closure motion. No SAP premise. |

C34–C36 and final C45–C46 source assembly are owned by the parent stream.
The explicit homogeneous model diagnostics C49 are owned by the separate
boundary stream; the local C47/C48 mechanisms above do not certify those
model constructions.

## Representation and scope

`NamedProjection` contains an ACTUAL `Term L source target`; its map is literal
`typedEval`, with surjectivity and noninjectivity as the actual quotient/kernel
conditions. `NamedProjection.quotientEquiv` proves the target is the actual
kernel quotient. `NamedQuotientSystem` is registered projection DATA, not an
assumed fibre-avoidance, fresh-frame, homogeneity or completion provider.
`KernelClauses` separately states the two mathematical hypotheses for precisely
those existing named projections. Necessity proves those clauses from SAP.

A strict projection has a nonempty source, proved from its noninjectivity;
no extra source nonemptiness assumption is added. The arbitrary-signature
primitives and actual named terms come from the parent's foundation commits.
No B037/B038 code or unaccepted external theorem is imported.

## Validation

Eleven new Lean modules, 928 lines at mathematical stream freeze
`5a9b884`; all passed their targeted incremental builds. The last individual
checks were actual `NamedNecessity` / `SAPNecessity` and finite sequential
avoidance. The final narrow union of AFF, SAPNecessity, Sequential and
Uniformity passed **1344 jobs** (runtime/b039-quotient-final-union.log). Only existing accepted B010 linter warnings were replayed; no new
proof hole, mathematical axiom or broad Mathlib/tactic import is introduced.
The owner remains responsible for the one final whole-package pipeline,
transitive audit, independent source review, exact-head CI and actual green
resulting-main acceptance. This report does not assert those pending gates.
