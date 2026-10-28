# B002 — takeover fan/Helly implementation checkpoint

28 October 2026. B002 remains **IN_PROGRESS**, not submitted or accepted.
The live `coordination` STATE is the sole claim authority. This report
records implementation evidence, not a claim transition or independent review.

## Preserved history and exact candidate

- Original author: project 1. Existing branch `project1/B002-raw-exact`, PR #3.
- Handoff head retained in full: `85878128003ace4d4e63d2a42a1cbcb596857308`;
  its CI 40665192487 failed in proof bodies before any import migration.
- Last actual green predecessor retained:
  `5254d3a5f2455c97710aa554c884052ac84cd257`, CI 40664176515.
  The older `fe7de6c` entry in the historical submission is not the final green checkpoint.
- Local takeover branch `takeover/B002-cco-helly` preserves all original history.
- Import-only ancestry: existing PR #5 `df2dbc4c` merged as `806ca58`, then
  consumer/tactic cleanup `61ba25625e726150172405e8adf34a3e1fa82cd2`.
  These changes preserve all proof bodies after removing import lines.
- Inherited proof repairs: `d40807b`.
- Actual full C13 source proof and consumers: `e83c1d9`.
- Source-quantifier/C06 checkpoint:
  **`a1f41138d864cd852f635beed54a582c50d2c180`**.

No original WIP work was reset or discarded. Source pin
`490c3f36d85db5a0b3ced0598e6c431825254ec5`, mathematical contracts,
Lean 4.34.1 and the exact Lake manifest remain unchanged.

## Actual source-to-Lean discharge

| Claim | Current proved source export / mechanism |
|---|---|
| C06 | `WordThetaSource.wordTheta_cycleHom_of_pairwise`: arbitrary finite indexed RAW word profiles at one actual target, with separate nonemptiness and pairwise **distinct** compatibility. All word lengths and identity letters are retained; positive-length endpoint gluing is explicit in `wordThetaOccurrence_finish`. The existing private-fan vertices keep all interiors private and merge duplicate direct spokes by proved atom uniqueness. |
| C07 | `ExactCalculusSource.wordProfileHelly_pairwise_of_CCO`, plus the existing `WordProfileHelly` interface: arbitrary finite same-endpoint word profiles, including zero/identity and empty families. No Helly provider remains assumed in the source export. |
| C08 | `ExactCalculusSource.exactMenuHelly_of_CCO`: flatten finite exact menus, including the empty family. Existing representation/converse/meet closure is unchanged. |
| C09 | `ExactCalculusSource.convolution_of_CCO`: actual composition equals the finite pair-word presentation for nonempty exact factors; empty restriction lists are included. |
| C10 | `comp_exact_meet_right_of_CCO`, `comp_exact_meet_left_of_CCO`, `fullExact_saturation_meet_distribution_of_CCO`: the actual resulting meet must be nonempty. No law for empty resulting intersections is asserted. |
| C11 | Existing `Balls` pair criterion and source coseriality are unchanged. |
| C12 | Existing `FanAllCycles` and `FanCCOCompletion` are now usable through the repaired downstream trace proofs. A root-free cycle uses the actual punctured reference map; a root-containing cycle replaces precisely its two root-incident word walks using pairwise witnesses. This proves all cycles without needing an extra cycle-classification provider. |
| C13 | `ExactBallHellySource.exact_ball_helly_of_pairwise_CCO`: arbitrary finite heterogeneous exact balls, arbitrary original centre sorts, repeated actual centres, identity-only words, empty menus and empty/singleton families. Only original `HomogeneousSource S G` and `SemanticCCO S` are assumed. Self-intersections are derived by source coseriality; pairwise hypotheses require distinct indices only. `heterogeneousExactBallHelly_of_CCO` discharges the existing Type-0 provider via a finite `ULift`. |

C06 is **not yet complete**: its contract additionally requests an explicit
classification theorem saying every whole simple theta cycle consists of
two private paths. `WordThetaSource` constructs the actual arbitrary-length
theta and proves every cycle has a source homomorphism through the stronger
two-root-spoke argument; it does not export that whole-cycle classification.
This remaining C06 obligation is not needed to discharge C12/C13.

The readout has three explicit steps. `FanHomTraceColours` preserves each
original typed atomic edge and recovers the whole real trace certificate.
`FanHomWords` reconstructs the original RAW relation at the completed root
and marked-centre images, without assuming diverse outputs. Finally C13
uses **one** original automorphism from `FanCentreColours` to align all
centres. A zero-diversity restriction is handled first by `ZeroWordHelly`.
There is no SAP, quotient homogeneity, section, tuple-lifting axiom or
assumed full Helly conclusion in this proof.

## Inherited failures versus import changes

`WalkCertificateTransport` had an impossible singleton case left open and
an extra induction-hypothesis argument. `FanHomWordTrace` attempted to erase
a nontrivial `Fin.cast` using `simpa`; the repair uses actual list extensionality.
`FanCentreColours` confused a Sigma tag equality with its point equality and
left an injectivity proof argument unparenthesized. Repairing those upstream
files exposed two further inherited `FanHomTraceEndpoints` issues: rewrite
order at the start, and whitespace before dependent indexed lookup at the finish.
All these repairs preserve the intended theorem hypotheses.

The separately tested import-only baseline had exactly the original three
failing modules; it introduced no import regression. The completed candidate
build now includes the two newly exposed downstream repairs as well.

## Local verification on the exact source checkpoint

Pinned compiler: Lean 4.34.1, commit `5045d0056413266e57c625dcd7c365b10e377c52`.
The runtime uses a narrow host `/proc` compatibility shim for the compiler's
own executable-path lookup; it does not modify Lean, the toolchain or imports.
Pinned Mathlib revision: `d13f23b723b8a846827a245b89c10fc7d3f11612`.

At `a1f41138d864cd852f635beed54a582c50d2c180`:

- Complete `lake build`: **success, 932 jobs**. No broad `Mathlib` or
  `Mathlib.Tactic` import remains in the candidate CCO tree.
- A prior no-change incremental build at `e83c1d9` finished successfully in
  1.29 seconds; the source-quantifier/C06 update rebuilt four CCO modules and
  finished successfully in 4.57 seconds. These are local observations, not
  cross-environment benchmarks.
- Transitive `Lean.collectAxioms` audit of **all 1,456 declarations originating
  in imported CCO modules**, including private/generated names: success;
  only `propext`, `Classical.choice`, `Quot.sound`.
- Explicit `#print axioms` for C13, source word Helly, convolution and
  saturation distribution confirms the same allowlist.
- All five new public modules are imported from root `CCO.lean`.

The audit selects declarations by originating module (`env.getModuleIdxFor?`
and `env.header.moduleNames` with prefix `CCO`), then calls `collectAxioms`
transitively for each. Merely counting namespace-prefixed names would omit
private/generated declarations, and is not the reported 1,456 count.

Remote exact-head CI, independent mathematical review, current-main ancestry
and the global integration procedure remain mandatory before any merge or
acceptance. Local green does not mark this whole package complete.

## Concrete remaining work

This checkpoint closes the general fan/Helly bottleneck. It does **not**
complete B002 C20–C28. The existing quotient algebra and request APIs still
need their actual exact-kernel/source instances and finite joint structure,
then back-and-forth with all quotient anchors, actual quotient age triangle
fullness/AP, private-path quotient cycle transport and semantic CCO. The
new C13 theorem may now discharge their explicit Helly premise; it does not
automatically discharge those separate obligations.
