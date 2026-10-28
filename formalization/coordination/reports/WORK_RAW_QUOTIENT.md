# Work team B002 quotient checkpoint

Source pin: `490c3f36d85db5a0b3ced0598e6c431825254ec5`.
Implementation starts from the preserved B002 handoff head
`85878128003ace4d4e63d2a42a1cbcb596857308`; no historical WIP was reset.
This is an isolated LOCAL takeover candidate, not a package submission.

## Source/API map

Pinned `sections/exact_foundations/03_joint_exact_sort_lifting.tex` has
blob `394e0db063a476c5c069384b3d3fa2ffd3c7471d`;
`02_exact_quotient_orbital_geometry.tex` has blob
`d462f2bfffcd67c1fa712ac516972ab18e073d44`, matching the public catalogue.
Actual N07/N08 proofs and existing `JointPoint`, `QuotientRequests`,
`AtomicExact` and `ConvolutionFromHelly` signatures were read.

- `ActualOrbitalExact.actual_pair_colour_exact` constructs a nonempty
  exact presentation of the optional colour of EVERY actual original
  pair. The `none` case forces literal tagged equality, hence a genuine
  same-sort identity word. It does not invent a cross-sort equality atom.
- `actual_original_orbital_exact` identifies this constructed presentation
  with the entire actual group pair orbit by original homogeneity.
- `exact_actual_request_of_helly` constructs the actual real-to-quotient
  request from its exact kernel and the C09 convolution theorem. Thus the
  former arbitrary atomic/request presentation providers are discharged.
- `JointExactRequests.joint_real_point_requests_of_exact_kernels` supports
  arbitrary finite index universes by reindexing through `Fin`. It chooses
  only the displayed representatives of actual equivariant surjections.
- `JointFiniteExtension.FiniteJointPartialIso` represents an actual finite
  domain of tagged quotient values, a map retaining every named sort, and
  preservation of all complete actual pair orbitals. `injOn_image`
  derives injectivity from these orbitals, without SAP or freshness.
- `finite_joint_extension_of_exact_ball_helly` extends this finite partial
  isomorphism by any designated quotient point `π k x`. The new domain is
  exactly the old domain together with that point, and the map agrees on
  its whole previous domain. Every old/new, new/old and diagonal orbital
  is preserved. The identity quotient gives C20's original real-point
  extension as a special case.

The only remaining source provider in these extension exports is the
explicit `HeterogeneousExactBallHelly S` (C13). Exactness of the ACTUAL
quotient kernels, surjectivity and equivariance are genuine input data,
not assumed quotient lifting or an assumed source theorem.
The source-strength C13 proof is being supplied independently by the
B002 fan task; an integration corollary must discharge the provider.

## Validation and exact limits

All three new production files compile locally with the pinned
Lean `4.34.1` (compiler commit `5045d00`) and manifest dependency revisions,
using the B002 + PR5 targeted-import compatibility build products and an
independent output directory. A runtime `/proc/self/exe` compatibility
shim is needed in this host, as documented by the infrastructure task.
No `sorry`, `admit` or new mathematical axiom is used. All new modules are
imported from root `CCO.lean`.

The combined whole-branch CI/audit and independent review are still
required. Local compilation does not certify the currently failing
historical fan modules or the entire B002 package.

C21–C28 remain OPEN. In particular, `HomogeneousSource S G` for an
arbitrary named group `G` proves only finite tuple extension. A countable
back-and-forth limit need not be an element of that arbitrary `G`.
C21 must construct one actual sort/colour-preserving automorphism of the
original source and prove its action on actual quotient classes, rather
than adding a closure hypothesis or claiming membership in `G`.

## Actual original back-and-forth checkpoint

The following additional modules now compile locally with the same pinned
compiler and dependency build products:

- `JointOrbitalGraph` gives actual finite joint orbital graphs, their
  genuine inverses, single-valuedness/injectivity, and exact-kernel
  one-point extension. The graph is an auxiliary representation of the
  already defined `FiniteJointPartialIso`.
- `JointCountableBackAndForth` uses the targeted
  `Mathlib.Order.Ideal.idealOfCofinals` theorem for a two-sided countable
  back-and-forth. It constructs sortwise bijections preserving all
  actual pair orbitals and every initial finite graph row.
- `JointCountableExtension` explicitly supplies this extension mechanism
  from the actual kernel/C13 theorem, and extends the original finite
  partial-isomorphism representation.
- `ActualJointLifting.actual_joint_lifting_of_exact_ball_helly` includes
  original real slots as genuine identity quotients, constructs one
  `OriginalAutomorphism S` (bijections of the original sorts preserving
  their actual binary colours), and proves that this SAME original
  automorphism induces the quotient bijections on EVERY actual class.
  The mixed orbital of `(x, π x)` forces the projection equation.
  All originally displayed finite-map values are retained. This proves
  C21 conditional only on true C13 and the exact quotient input data;
  it makes no false assertion that the limit lies in arbitrary `G`.
- `EquivariantUnaryLifting.actual_joint_unary_lifting_of_exact_ball_helly`
  proves that the same lift preserves every added ACTUAL equivariant
  unary map globally. It therefore extends an expanded finite closed
  partial isomorphism on exactly its original displayed vertices (C22),
  without adjoining arbitrary representatives to that finite domain.

Original-sort countability and a finite list of actual quotient sorts
are explicit in these signatures, exactly as in N08. Every quotient's
countability is derived from its actual surjective original projection.
The original source sort family is finite by `AtomicSource.finiteSort`.
No source mathematical contract or accepted signature has been changed.

The previous OPEN marker for C21/C22 is superseded by these actual proofs,
but they remain CONDITIONAL on C13 within this isolated checkpoint until
the fan source proof is merged and the source-strength corollaries compile.
C24–C28 remain OPEN. Combined exact-head CI, axiom audit and independent
non-author review remain required before any package submission.

## Source providers discharged; combined local checkpoint

The preserved fan/source checkpoint
`b7e7b05481e6b9477fa4d9b84194e8d506617d80` and the actual lifting
checkpoint `2f4a6c3` were combined by the history-preserving merge
`c7ccffa9c43f0fd0e3b911627094ab768738746e`.
`JointLiftingSource` now applies the genuine
`heterogeneousExactBallHelly_of_CCO` provider and exports:

- `finite_joint_extension_of_CCO` (C20);
- `actual_joint_lifting_of_CCO` (C21);
- `actual_joint_unary_lifting_of_CCO` (C22);
- `one_sort_joint_lifting_of_CCO` (C23).

These are source-strength statements under original homogeneity and
semantic CCO, with original countability where back-and-forth requires
it, and with actual equivariant surjective quotient projections whose
kernels have genuine full-exact presentations. No Helly, atomic-request,
back-and-forth, quotient-lifting, or arbitrary-group closure provider
remains assumed in their signatures.

Validation of the combined code: `lake build CCO` succeeded, 981 jobs.
The transitive module-origin audit (including private/generated CCO
constants) checked all 1,544 CCO declarations, allowing only `propext`,
`Classical.choice`, `Quot.sound`. Explicit transitive axiom prints for
all four new source exports report exactly that trio. The source pin,
toolchain and manifest remain unchanged.

The C21/C22 conditional status above is now superseded by these source
exports. C24–C28 are still OPEN; C06's separate whole-theta cycle
classification is also explicitly OPEN in the fan task's report.
This remains an IN_PROGRESS combined B002 checkpoint, not a submission
or acceptance. Remote exact-head CI and a substantive independent
non-author source/API/provider/consumer review remain mandatory.
