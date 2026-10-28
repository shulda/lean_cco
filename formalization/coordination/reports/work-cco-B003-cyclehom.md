# B003 takeover: actual cycle homomorphism and source Helly

Local proof checkpoint: `d2fcfea6ed513bc9b6286a9adf7be433d9790072` on
`takeover/b003-cyclehom`. This is a recoverable local checkpoint, not a
public claim, submission, or remote-CI certificate. PR #4 and the original
`p2-b003-strong-exact` history are retained. Original project 2 authored the
inherited geometry through handoff head
`f140b2caf36d912f9d60f84727ba7674b8b7205a` (green run 40668681157).
New proof implementation: Work team actor `strong_bridge`; genuinely
non-author review is handled separately by `independent_review`.

The candidate merges the existing PR #5 exact import fix
`df2dbc4cb3391f74c289dd677a233932e9ab4bd8` and cherry-picks only the four
B003 consumer import fixes from `1e0ac1d2547a5a327378a2c5ec8ffb34badeea04`.
No shared foundation proof or mathematical contract is changed. Source pin
remains `490c3f36d85db5a0b3ced0598e6c431825254ec5`.

## New proved source chain

- `ThetaPairLineMap`: construct an actual typed point map from the two
  literal real word lines at common roots. Agreement at every original
  position includes both transported root values. The second branch uses
  its proved distinct occurrence tag. Arbitrary original points on
  off-cycle branches carry no edge-preservation assertion.
- `ThetaCycleHom.thetaCycleHom_of_SAP`: every genuine simple long-theta
  cycle receives an actual `CycleHom` under original `HomogeneousSource`
  and `AgeSAP`. Half-open cyclic intervals cover every step, including
  both roots and the final wrap. Forward letters use the original old
  atoms; the reverse arc uses actual diagram and source converses.
- `thetaCycleCompatibility_of_SAP` and `hardThetaProvider_of_SAP` discharge
  the two existing explicit geometric predicates, using no CCO or Helly
  premise to manufacture the cycle witness.
- `wordHelly_of_SAP_CCO` discharges `WordHelly` from original homogeneous
  SAP plus semantic homomorphic CCO. Existing reductions include empty,
  at-most-two and direct-single-letter families. SAP injectivization,
  rather than the initial CCO homomorphism, separates the two roots.
- `SourceExactCalculus`: original-source exact-menu Helly, full exact
  convolution, exact product closure, and both finite exact-meet
  distribution directions. Every `WordHelly` input is discharged. The
  evaluated factor/meet nonemptiness guards and typed Top conventions
  remain explicit; no artificial STRONG identity enters.

This closes the word/exact-menu Helly and C08 source-provider seam. It
DOES NOT close full C07 endpoint-survivor realization, C09 three-root
sufficiency, C12 completion/path formula, C13 classification, or the
independent AP+CCO triangle-fullness result. B003 remains `IN_PROGRESS`.

## Validation and limits

Exact pinned Lean `4.34.1`, compiler commit
`5045d0056413266e57c625dcd7c365b10e377c52`, and unchanged lake manifest.
Local full-root `lake build` succeeds (1012 jobs, with unchanged existing
warnings); all three new public modules are imported by `CCO.lean`.
The transitive local allowlist audit checks all **1499** CCO declarations,
including private names, and permits only `propext`, `Classical.choice`,
`Quot.sound`. Explicit `#print axioms` for the actual CycleHom, source
WordHelly, and exact-product consumer gives only that same allowlist.
No sorry/admit/new mathematical axiom or stronger source hypothesis is used.

The local runtime uses the documented environment shim only to resolve
Lean's own executable in the nested process namespace. Remote exact-head CI
and a committed exact-SHA independent disposition are still required before
any submission/integration. The local report does not certify either.
