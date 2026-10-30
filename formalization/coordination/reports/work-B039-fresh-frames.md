# B039 actual unary fresh frames and relative kernels

Source pin: `490c3f36d85db5a0b3ced0598e6c431825254ec5`.
Actual source: `sections/unary_fresh_frame_sap.tex` and the selected
`lem:unary-homogeneous-sap-criterion` in `sections/finite_orbit_avoidance.tex`.
Only mathematical prerequisite: ACCEPTED B010, specifically the abstract
finite-action avoidance theorem in `CCO.AclOwners.Avoidance`.

## Actual source status

All fifty claims, twelve definitions and five principal source results are
implemented. The source/consumer union passed 1349 narrow build jobs; the two
complete actual C49 model streams passed their respective 1340/1341-job
consumer builds. The final exact source is not yet accepted: the complete
frozen receiving pipeline, independent exact-head review, public CI and
resulting-main CI/audit remain required.

The public aliases are all in `CCO.UnaryFreshFrames.Source`:

| Source label | Exact export |
|---|---|
| `lem:foundational-real-frame-orbits` | `foundational_real_frame_orbits` |
| `lem:unary-homogeneous-sap-criterion` (UA) | `unary_homogeneous_sap_criterion` |
| `lem:foundational-quotient-fibre-avoidance` | `foundational_quotient_fibre_avoidance` |
| `thm:typed-abstract-fresh-frame-sap` (AFF) | `typed_abstract_fresh_frame_sap` |
| `cor:typed-abstract-relative-kernel-sap-iff` (RK) | `typed_abstract_relative_kernel_sap_iff` |

The separate `Structure.fresh_frames_hidden_acl_sap` proves the explanatory
source remark. No sixth numbered result is claimed.

## Definition map

All names below are inside `CCO.UnaryFreshFrames`, usually its `Structure`
namespace. `Language` and actual well-sorted `Term` syntax are primitive data.
Functions are unary and total on their input sort, extended canonically by
the identity off that sort. This extension changes no typed term or actual
automorphism condition. There are no nullary function generators; arbitrary
relation arities, including zero, are retained.

| Definition | Actual Lean representation |
|---|---|
| D01 actual term closure | `Structure.eval`, `closure`, `closureAt`, `Closed` |
| D02 actual stabilisers/equivariance | full `Structure.Aut`, `fixer`, `aut_closure`, `fixer_closure_eq` |
| D03 orbit acl/dcl | `Acl`, `Dcl`, `orbitOver`, direct full-group variants in `SAPAlgebraicity` |
| D04 actual fresh frames | `Structure.FreshFrames` |
| D05 closed-base infinite orbits | `Structure.InfiniteClosedOrbits` |
| D06 entire hereditary age/SAP | `Structure.Piece`, `Piece.Embedding`, `Homogeneous`, `AgeSAP` |
| D07 actual kernels/fibres | `Quotient.KernelLe`, `FibreValues`, actual named `NamedProjection` |
| D08 actual relative index | `Quotient.fibreKernelEquivValues`, `arbitraryFibreValuesEquiv` |
| D09 semantic typed term functions | `Structure.NamedFunctions`, `typedEval`, `namedValues_eq_closureAt` |
| D10 forced/unforced clauses | `Structure.ForcedNamedFactors`, `InfiniteUnforcedIndex` |
| D11 finite sequential requests | `NamedQuotientSystem.finite_sequential_choices`, `finite_sequential_avoidance` |
| D12 actual RK condition | `NamedQuotientSystem.KernelClauses` and the real-base full-Aut acl equality in the RK export |

`NamedProjection.quotientEquiv` proves that the target really is the quotient
by the actual kernel of its surjective named term. The system contains an
arbitrary actual covering family of existing named projections. All kernel
clauses quantify over the actual terms of the source language, not over all
conceivable equivariant maps. A proper covering family already suffices for
the stronger core theorem; the full declared source family instantiates it.

## Claim map and discharge paths

| Claims | Actual proof modules and content |
|---|---|
| C01–C03 | `Language`, `ClosureActions`: actual typed terms, singleton additivity, empty closure, closed unions, equivariance, literal stabiliser equality and orbit acl/dcl |
| C04–C06 | `Frames`: SAME actual subgroup in both directions; one B010 avoidance move on the whole surplus closure; `FullFrames` proves the full-Aut source remark |
| C07 | `SAPBoundaries`: actual countable pure-Nat homogeneous SAP structure, with its proper identity subgroup having singleton off-closure orbits |
| C08–C10 | `SAPFresh`, `SAPCopies`: strong same-base copies, arbitrary finite families, explicit distinct full-Aut orbit witnesses and genuine orbit infinitude |
| C11–C17 | `Age`, `SAPAvoidance`, `SAPAlgebraicity`: all finite closed pieces including orphan hidden bases, actual aligned closed union, strong intersection and full-Aut UA criterion |
| C18–C21 | `Quotient.Fibres`, `Named`, `Uniformity`: actual named semantic function finiteness derived by evaluation at one point, actual fibre-stabiliser orbit equality and actual fibre-kernel quotient equivalence |
| C22–C26 | `Quotient.Avoidance`, `NamedAvoidance`: ONE common motion, all unforced values avoid the finite forbidden set, forced literal named values retained, exact singleton-closure intersection and freshness |
| C27 | `Quotient.Sequential`: actual finite requests on different sorts, injective representatives and every new unforced value avoiding entire earlier singleton closures |
| C28–C33 | `Quotient.System`, `AFF`: actual named representations, finite induction on every hidden A point and exact AFF; no homogeneity or orbit premise occurs in this construction |
| C34–C35 | `FullFrames`, `Source`: only after AFF use FULL-Aut real-base infinitude, deriving all hidden full-Aut acl=dcl=cl and actual hereditary SAP |
| C36 | `UniformBounds`, `Source.source_uniform_real_bound`: finite original real sorts and transitivity derive actual FINITE singleton bounds; singleton additivity gives the linear bound in the generator count |
| C37–C44 | `Quotient.Necessity`, `NamedNecessity`, `SAPNecessity`: FULL-Aut fixed/finite fibre orbits and actual subgroup motions; SAP discharges full-Aut closure equality and BOTH kernel clauses |
| C45–C46 | `Source.typed_abstract_relative_kernel_sap_iff`: actual sufficient AFF direction and actual SAP-only necessity, with the unchanged final source scope |
| C47–C48 | `Quotient.NamedNecessity`: actual local definable-off-closure and finite-index algebraic-off-closure witnesses without assuming SAP |
| C49 | `Examples/Matching*.lean`, `Examples/TwoCover*.lean`: both ORIGINAL finite signatures, actual countability, all finite-closed homogeneity, local finiteness, real-base full-Aut infinitude, every hidden named proper quotient representation, exact separated kernel-clause failures and actual failure of SAP. Any auxiliary root predicates are proved conservative on EVERY original closed partial embedding, with literally equal full-Aut subgroups |
| C50 | `SAPBoundaries`: actual nullary empty-base obstruction and two separately binary-closed finite factors with a nonclosed union |

Generic elementary fibre lemmas accept equivariant maps because their proof
uses only group actions. Every source instance is supplied by `Named` from
actual typed term syntax. No new principal provider is an input. Finiteness of
semantic term functions is DERIVED from actual finite singleton closure and
transitive G, not assumed as a replacement for those source hypotheses.

The actual subgroup G and full Aut(H) are kept distinct throughout. Both
stabiliser orbits of a named term value equal the same actual fibre-image set;
full-Aut finite invariance gives algebraicity, while an actual G-fixer motion
proves nonmembership in named closure. Neither kernel clause is assumed in
the SAP necessity direction. A named term, not a set-theoretic factor, is
extracted from literal singleton-closure membership and globalised by G.

`FinalScope` retains actual countability, finite named language, full-Aut
oligomorphy, finite-closed homogeneity and local finiteness. These are exactly
the final structural source scope, not a provider for AFF or SAP. The generic
frame and fibre theorems require only their weaker stated source premises.

## Provenance and validation

Actual implementers: `/root/b039_fresh`, `/root/b039_fresh/sap`,
`/root/b039_fresh/quotient`, `/root/b039_fresh/examples`; root coordinates
publishing and integration. No implementation author is used as reviewer.
Coherent source is backed up by root with exact source-tree correspondence.

Only narrow real Lean consumer builds have run during implementation. No
whole receiving pipeline, whole audit or public exact-head CI is claimed at
this source freeze. Accepted B038 main
`709931c1d7bae96f549efcf658d795d38dc1e9e8` was merged once, preserving the
entire accepted `CCO.lean` prefix and all source history. Its validated CCO
children and Ramsey provider artifacts were privately copied for incremental
validation; the changed CCO root artifact was not copied. A concrete stale `FullFrames` generated artifact was caught
by a real consumer, moved reversibly to `runtime/b039-stale-fullframes`, and
rebuilt with artifact restoration disabled. Root subsequently changed only
the local runtime default; production workflow, toolchain and manifest remain
unchanged. No broad fallback or repeated blind installation attempt occurred.
