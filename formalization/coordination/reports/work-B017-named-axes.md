# B017 actual entire named finite axes — C16–20

Actual implementation author: `/root/b009_inheritance` (reused after completing
the independent B009 inheritance branch). Root supplies the pure canonical
Goursat and rank-count modules. `/root/b017_kernel` supplies the actual general
binary-source foundation and subgroup-to-F2 conversion. No implementer acts as
the batch's independent reviewer.

Source pin: `490c3f36d85db5a0b3ced0598e6c431825254ec5`.
Actual source: `sections/simultaneous_typed_exact_quotients.tex`,
`lem:typed-finite-entire-axis-projection` and
`cor:typed-finite-linear-goursat`, with finite_kernel N04/A06/A07.

## Actual source, scope and hypotheses

`NamedAxes S I` names each entire axis by a literal unary predicate of the
original `BinaryStructure X`. These predicates define pairwise disjoint finite
sets. They DO NOT have to cover X. Other points and other named sorts may form
an arbitrary infinite complement. Empty named axes are allowed.

The acting group is the FULL original `S.Aut`. Each `Intrinsic i` is the FULL
automorphism group of the actual finite induced axis, preserving every unary
predicate, binary direction and binary loop. The local restriction, pair image
and selected finite image are actual group homomorphisms/ranges. There is no
owner-partition or owner-kernel premise and no finer-source image substituted
for full Aut.

Only actual original `S.Homogeneous` is required for C16/C17/C20. It extends an
injective finite original partial isomorphism; no countability, symmetry,
transitivity, CCO, SAP, exactness or owner-expanded homogeneity is assumed.
A07 additionally supplies actual group isomorphisms
`e_i : Multiplicative V_i ≃* Intrinsic i` for finite-dimensional F2 modules.
No additional linearity of actual group images is assumed.

## Source-to-Lean map and discharge

- `Named/Axes.lean` constructs actual full-group `restrict`, `actualPair`,
  `projection`, `actualImage`. `unionEquiv` identifies just the FINITE selected
  whole-axis union with its disjoint coordinate sum. The coordinate tuple
  induces a genuine permutation of this union.
- `finite_extension` checks every unary/within-axis binary instance using the
  actual intrinsic automorphism, and every ordered cross binary instance using
  an ACTUAL full-group pair witness. Ordinary original homogeneity extends this
  actual finite partial map; the complement is left to that extension theorem.
  `finite_projection` is the genuine C17 finite image/pair-marginal equality.
- `restrict_surjective` derives C16 using the singleton instance. The actual
  pair image is then subdirect over the FULL intrinsic groups, as a conclusion.
- `actual_graph_transport_flat` proves C20 using one actual full-group lift
  of each chosen first-coordinate motion. It needs no commutativity or F2 and
  does not assert a cocycle identity for arbitrarily chosen pair maps.
- `Named/LinearSource.lean` transports each actual pair image by the supplied
  group representations. The owner's F2 subgroup utility proves scalar closure
  from the actual subgroup laws and the two scalars, so it is a genuine
  submodule. C16 supplies its two surjective projections; root's canonical
  Goursat theorem therefore applies to THIS actual submodule. The two kernels
  are exactly the motions paired with identity. Both common-quotient checks
  are onto, including a zero common quotient.
- `Named/CheckSource.lean` forms EXACTLY ONE orientation of each unordered
  distinct pair in the finite selected set, using a finite enumeration only.
  No ordering of the entire index family is assumed. The row formula is the
  literal F2 sum of its two endpoint quotient checks. `linearImage_eq_check_kernel`
  instantiates the genuine C17 actual-source equality; reverse orientations use
  the actual pair image transpose, not an arbitrary map-coherence assumption.
- `linearImageEquivActual` is an explicit bijection with the ACTUAL finite
  restriction IMAGE of full Aut. `actualImage_finite` proves it finite FIRST.
  `actualImage_rank_count` transfers root's checked finite-kernel rank formula
  and counts THIS image as `2^(sum of coordinate dimensions - rank Phi)`.
  It never counts the possibly infinite full group Gamma.
- `Named/Boundary.lean`: the empty image has its unique empty tuple; empty
  and singleton selected sets have no pair rows; an empty actual named axis
  has a trivial intrinsic group. These are literal original-source consumers.

All C16–20 providers are genuinely discharged. In particular the final
actual rank consumer assumes neither a finite-projection provider nor
subdirectness/linearity of supplied abstract pair groups.

## Validation and integration

Final owned target `lake build CCO.FiniteKernel.Named.Boundary` passed
1690 jobs with the pinned Lean 4.34.1/Lake and unchanged locked manifest.
It imports actual axes, actual linear-source/check-map consumers and root's
Goursat/rank modules. Only targeted imports were added. The batch owner runs
the ONE final whole root build, official transitive standard-three axiom audit,
complete current-source/actual-byte guards and external exact-head/main CI.
This implementer did not repeat another author's whole build or review.

Owned files: `Named/Axes.lean`, `Named/LinearSource.lean`,
`Named/CheckSource.lean`, `Named/Boundary.lean`. Root owns
`Named/Goursat.lean` and `Named/RankCount.lean`; the countercontrol helper owns
only `Countercontrols/` C21–22. No file overlaps remain.
