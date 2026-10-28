# B013 C05 — actual relative loop criterion

Actual implementation author: `/root/b009_fibres/class_intervals`.
The same author previously implemented B009 class intervals and localisation;
this is implementation, not independent review.

Base: accepted main `0cbeb4e47cf3f7997214ee5c3dd25f8f0fda3a94`.
The stable parent `Basic.lean` commit `df6f972` was cherry-picked without
changes as `0b5cadd`; it defines the actual guarded `FiniteIndex` and
whole-orbital `AtomBelow` predicates. No unaccepted sibling mathematics is
used beyond that same-batch stable definition interface.

Source pin: `490c3f36d85db5a0b3ced0598e6c431825254ec5`. Read actual
`sections/finite_packets.tex` (blob
`dd3e608f03e7c5b1b1854a45de462859f8355143`), the B013 contract,
finite_packets C04–C05 and N02. The finite Ramsey correction is the stated
N02 expansion of source `lem:loopcrit`; no infinite Ramsey theorem is used.

The owned module is `CCO/FinitePackets/Geometry/LoopCriterion.lean`, namespace
`CCO.FinitePackets.Geometry`. It imports only the stable same-batch Basic
interface and accepted `Canonical.Loopless` / `Canonical.RamseySubset`.

* `atomBelow_of_colour`: one actual old pair in an invariant equivalence
  yields inclusion of its WHOLE old diversity orbital by colour invariance.
* `relative_no_looped_no_embedding`: from an embedding of precisely the
  original source triangle Ramsey number into the ACTUAL quotient
  `RelativeClass J.val K.val x`, choose `Quotient.out` representatives in
  that one K-class. Representatives are injective and pairwise J-inequivalent.
  Accepted finite triangle Ramsey returns a looped original atom in K;
  the no-outside-loop premise puts it in J, a contradiction.
* `finite_relative_of_no_looped`: establishes `Finite` on that actual
  quotient first, then bounds `relativeIndex` strictly by
  `sourceTriangleRamsey S`. This direction uses no H or CCO and works for
  an empty diversity palette.
* `looped_relative_clique`: accepted original triangle-full clique
  construction is applied with the EMPTY real anchor. For each n, an
  actual (n+1)-vertex monochromatic clique is moved by original homogeneity
  so its last point is any requested real x. The other n vertices give
  an injection `Fin n ↪ RelativeClass J.val K.val x`; K-membership uses
  the old atom and inequivalence uses whole-orbital colour invariance.
  In particular this handles n=0 without a distinguished element of Fin n.
* `finiteIndex_no_looped` contradicts the n = actual relative index + 1
  injection ONLY after installing the assumed actual `Finite` instance.
* `finiteIndex_iff_no_looped S H cco J K hJK` is the full C05 criterion:
  `FiniteIndex S J K ↔ ∀a, Looped S a → AtomBelow S K a → AtomBelow S J a`.
  The source statement retains J≤K. The two helpers in fact need no order
  premise because they count restricted J-classes inside a K-class directly.
* `relativeIndex_lt_ramsey_of_finiteIndex` exposes the quantitative source
  consumer for every actual class.

The source S has exactly `AtomicSource.{0,v,w} Unit (fun _ => M)`;
H is its actual homogeneous group action, and CCO is
`SemanticCCO.{0,v,0,w} S`. Only the actual clique direction uses H/CCO.
No SAP, exactness, countability, globalisation, synthetic quotient source,
assumed clique provider, or extra finite-class premise has been introduced.
Equality and empty-palette cases use the original optional colour semantics.

Validation: the pinned Lean 4.34.1 runtime, unchanged toolchain/manifest,
separate writable local build and existing mathlib package cache are used.
`lake build CCO.FinitePackets.Geometry.LoopCriterion` passes (1135 jobs).
The parent owns root imports, whole-batch build, official transitive axiom
audit/source closure checks, source map, remote publishing and final actual
non-author review. No public queue or root imports are changed here.
