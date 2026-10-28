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

## Finite group realignment leaf

`FiniteRealignment.finite_original_realignment` applies original finite
homogeneity to the real image tuple of a constructed original source
automorphism. `finite_quotient_realignment` projects this finitely aligned
real tuple through the actual equivariant quotient maps. Consequently
`finite_joint_group_lifting_of_CCO` supplies a genuine `h : G` inducing the
INITIAL FINITE joint partial map. This does not claim that the countable
back-and-forth limit lies in an arbitrary group G; no closure hypothesis
is used. The finite original representatives are auxiliary witnesses,
not extra displayed parameters or a coherent section.

Validation: root build succeeds (982 jobs); transitive module-origin
CCO audit succeeds on 1,547 declarations with only the standard three
allowlisted axioms. The earlier combined checkpoint `6e16e8a` remains
fixed on branch `work/raw-quotient`; this is an additive leaf on
`work/raw-quotient-age` for subsequent exact-head CI/review.

## C24 actual quotient triangle fullness

`QuotientTriangleFullness.ActualOrbitalDiagram` encodes a finite complete
named orbital diagram by ACTUAL full original-group pair orbits, with
logical diagonal equality, reversal and distinct-vertex separation.
`TrianglesLegal` means all local induced diagrams on at most three
vertices have actual realizations; repeated indices include the
zero/one/two-vertex boundary cases.

`actual_quotient_request_helly_of_CCO` constructs exact pulled-back
quotient orbital requests using actual source orbitals and the genuine
exact kernel presentations. True source C13 gives finite request Helly.
`actual_quotient_triangle_fullness_of_CCO` then proves the complete C24
realization theorem by induction over finite formal vertices. Local
triangle witnesses are transported to the already realized pair by a
G-element, so requests meet pairwise independently of chosen actual
representatives. Source C13 adds the next quotient point. Diagonal,
reversal and separation yield the entire injective realization.

No quotient homogeneity, pre-existing quotient CCO, SAP, arbitrary tuple
realization or additional source provider is assumed. Countability is
not needed by this finite proof. The standing source pin/contracts are
unchanged. The canonical actual quotient palette/source packaging is a
separate C28 obligation; `ActualOrbitalDiagram` already states C24 using
the full actual orbital relations, not an assumed abstract colour table.

This successor also cherry-picks the independently authored C14–C19
source modules (`ActualQuotientSource`, `FineColoursSource`,
`ActualNestedMaps`) from the fan task, preserving their reports. Local
combined root build succeeds (986 jobs). Transitive module-origin audit
checks all 1,583 CCO declarations against only the standard three axioms;
explicit prints for the C24 source theorem and finite G-lift agree.
Remote exact-head CI and independent review remain required. C25–C28
and C06's separate whole-theta cycle classification remain OPEN.

## Canonical actual quotient sort API for C26–C28

Pinned `raw_exact/module.json` declares C26, C27 and C28 in
`one_original_sort` scope. N09–N10 and `thm:exact-sorts-source` in
`sections/exact_foundations/03_joint_exact_sort_lifting.tex` concern
`M_E` for one original symmetric M. The earlier C21 theorem remains
fully typed over arbitrary original-sort origins. This distinction was
checked explicitly before fixing the following canonical API.

`CanonicalQuotients.Index family` is the subtype of the ACTUAL setoids
in `family : Finset (Setoid A)`. `Carrier k` is the actual `Quotient k.val`
and `projection k` is its actual quotient map. Exactness data give a
full-exact presentation of each actual equivalence relation; distinct
word presentations do not create distinct named sorts.
`projection_kernel` identifies the actual kernel, and
`sort_eq_of_injective_projections` proves that two identity-kernel
sorts are the SAME named sort. Thus the N10 identity-only cross-sort
exception is discharged structurally, not added as an unproved
nonduplication provider. No auxiliary identity copies from C21's
back-and-forth universe are present in this canonical quotient source.

`ExactData.invariant` derives quotient-kernel invariance from actual
source homogeneity and exact word presentations. The actual quotient
action and projection equivariance are proved. All definitions compile;
root CCO build succeeds (987 jobs) and transitive module-origin audit
succeeds against the standard three-axiom allowlist. Construction of the
finite actual quotient orbital AtomicSource and the remaining C25–C28
source-property assembly are still OPEN.

## Actual quotient tuple homogeneity and AP mechanisms

`QuotientFiniteHomogeneity` proves that every finite ACTUAL orbital graph
is induced by one original G-element. It explicitly converts the graph
to `FiniteJointPartialIso`, includes quotient-only finite domains in the
proved real-plus-quotient C21 theorem, and retains EVERY graph row.
`finite_quotient_tuple_lifting_of_CCO` gives the finite-tuple form,
including repeated values, without an injectivity or arbitrary tuple
realization provider.

`QuotientHomogeneousSource.actual_quotient_homogeneous_of_CCO` now derives
the complete accepted `HomogeneousSource` interface for a representation
P of the actual quotient orbital palette. Its explicit colour-orbital
representation equation is to be discharged by the actual palette
constructor, being implemented separately; it is not a new mathematical
axiom or an assumed quotient-homogeneity provider. All tuple universes,
sort casts, true diagonals and repeated values are retained.

`QuotientAgeAP.ageAP_of_homogeneous` proves actual induced-age AP: one
source automorphism aligns the entire common induced base, then the
actual finite union gives an amalgam. Images may intersect outside the
base. The additive `AgeAP` interface deliberately makes no SAP claim.
`quotient_ageAP_of_colour_orbitals` applies this genuine proof to the
proved quotient homogeneity bridge. The concrete actual quotient source
instance awaits the palette constructor and its colour-orbital equation;
these representation arguments must be discharged before reporting C25
or C28 as fully assembled actual source instances.

Local validation: full root `CCO` build succeeds (990 jobs). The transitive
module-origin audit checks 1,637 CCO declarations against only `propext`,
`Classical.choice`, `Quot.sound`, including explicit prints for the tuple
lifting, quotient homogeneity and age-AP exports. All new public modules
are root-imported. Source pin, accepted contracts, toolchain and manifest
remain unchanged. C26/C27 expansion is being implemented independently
using the canonical actual setoid family; full C06 classification and
the final C25–C28 actual source assembly remain OPEN.

## Concrete canonical source and C25 instantiated

The separately authored palette constructor has been cherry-picked from
`92c0c20226f567a0d664a9bd0d8eda4435d81870`, preserving its source/report.
`CanonicalQuotientSource.source S H E` now constructs the ACTUAL finite
canonical quotient `AtomicSource`. `source_colour_eq_iff_orbital` is proved
by that constructor; its representation equation is no longer an assumed
provider. The actual quotient actions are derived from E's exact kernel
presentations, so no invariant-kernel premise is left to supply.

`CanonicalQuotients.homogeneous` instantiates the entire accepted finite
source homogeneity interface from original H, original semantic CCO and
original countability. `CanonicalQuotients.ageAP` therefore proves C25
for the actual canonical quotient age, with no AP, quotient-homogeneity,
abstract palette, section or G-closure provider remaining. The concrete
C24 triangle-fullness theorem is instantiated on the canonical family.
All carriers and the finite total tagged quotient universe are countable;
nonemptiness and original-group transitivity of every actual quotient
carrier are proved. Finiteness, completeness, converse and same-sort
symmetry of the actual orbital language are fields of the constructed
AtomicSource, proved by the palette task.

Full root local build succeeds (992 jobs). The transitive module-origin
audit checks 1,676 CCO declarations against only the standard three
allowlisted axioms; explicit prints for the actual source, its
homogeneity, C25 AP and C24 triangle fullness agree. All modules are
root-imported. Exact remote-head CI and independent source/API review
are still required before package submission.

C28's source-property assembly still requires the actual semantic CCO
inheritance from C26/C27, being proved separately by the expansion task.
No such quotient CCO theorem is assumed here or reported complete.
C06's whole-theta cycle classification remains separately OPEN.

## Disjoint C26 cyclic deletion helper

`CyclicDeletion` reuses the existing `Fin.succAbove` skip embedding and
proves its exact cyclic-successor behavior: a surviving successor is
unchanged, or it bypasses precisely the one deleted position. The
complement enumeration, injection, nondeleted predecessor and successor
witnesses are all proved, including wraparound and reduced length one.
This is generic finite arithmetic for the separate cycle-compression
task, with no graph or completion premise. The file compiles clean;
root build succeeds (993 jobs) and the transitive module-origin audit
continues to allow only the standard three axioms.

## C27 raw cycle realization helper

The stable independently authored expansion commits `40ce985`, `a8c7f04`
and `25305a4` were cherry-picked to compile against their actual diagram,
reference-colour, whole-path and whole-menu-readout APIs.
`QuotientExpansionCycleRealization.CycleUsesEdge` records each actual
marked edge used by a source simple cycle. Given real marked points
satisfying the exact menus of EVERY such edge, the helper chooses actual
walks for all word occurrences on those used edges, retains reference
walks elsewhere, and glues the given marked points to the private walk
interiors. Actual source colours are unchanged along either orientation
of each word-path edge. `cycleHom_of_marked_edge_realization` therefore
proves a genuine raw `CycleHom`.

Its finite menu witnesses and positive word lengths are explicit premises
of this intermediate helper; the separate canonical C26 compression and
zero-word exclusion proofs must supply them before final C27 is exported.
No unconditional source CCO inheritance is asserted by this helper.
Full local root build succeeds (1,002 jobs); transitive module-origin
CCO audit checks 1,893 declarations with only the standard three axioms.
The file compiles without warnings and all public modules are root-imported.

## Actual C27 expansion menus and projected readout

`QuotientExpansionProjection.project_expansion_hom` proves the readout
for general typed original roots: one completed original expansion
homomorphism projects its marked points to a quotient diagram
homomorphism whenever the menus are the true full orbital pullbacks.
Both orientations are proved using the actual quotient source converse.

`CanonicalQuotientExpansion` DISCHARGES those menu and positivity data
for the concrete canonical actual source. Every specified quotient atom
gets its genuine nonempty full-exact original pullback presentation from
C14; missing edges receive an empty Top menu. Every listed word has
positive diversity length by the actual canonical zero-word exclusion,
whose identity-sort uniqueness is proved. `occurrence_specified` proves
that an existing private word occurrence belongs to a genuinely specified
quotient edge. `menu_holds_of_actual_edge` accepts EVERY choice of real
representatives of a correctly coloured actual quotient edge.
`project_completed` then projects a completed original expansion to the
actual canonical quotient diagram with all menu, nonemptiness, positivity
and representation premises constructed.

The original expansion homomorphism must still be obtained by the
separate C26 cycle classification/witness construction and original CCO.
No unproved all-cycle premise is omitted or silently promoted to a final
source C27 theorem here. Full local root build succeeds (1,004 jobs);
transitive module-origin audit checks all 1,917 CCO declarations against
only the standard three axioms. Explicit prints for menu representation,
positivity and completed projected readout agree. New files compile clean.

## Full finite-type and universe quantifiers for semantic CCO

`DiagramReindex` proves actual diagram pullback, simple-cycle transport,
cycle homomorphism equivalence and homomorphism pushforward along finite
index equivalences. `semanticCCO_of_fin` upgrades completion for EVERY
finite ordinal diagram to the full accepted arbitrary finite-vertex
interface. `semanticCCO_change_universe` reindexes through an actual
`ULift (Fin card)` and proves that the chosen universe of formal finite
vertices does not strengthen the CCO assumption. This permits Type-0
private expansion carriers from the pinned Type-v original CCO and avoids
silently restricting the final quotient CCO theorem to Fin diagrams.

The new file compiles clean. Full local root build succeeds (1,005 jobs)
and transitive module-origin CCO audit retains the standard three-axiom
allowlist, with explicit prints for both semantic CCO transport theorems.
The actual canonical all-cycle theorem and final C27 consumer are being
completed separately; this generic transport assumes no new source axiom.

## Final actual source C27 assembly (2026-10-28)

`CCO.RawExact.CanonicalQuotients.semanticCCO` in
`CanonicalQuotientCCO.lean` proves the complete semantic CCO interface for
`CanonicalQuotients.source S H E`, for an arbitrary finite family of
actual full-exact setoid quotients of one original source sort. Its only
mathematical inputs are the original homogeneous source `H`, original
`SemanticCCO S`, and the family's actual full-exact kernel data `E`.
There is no countability, menu representation, positivity, cycle-witness,
or quotient-CCO provider in the theorem's hypotheses.

For every finite ordinal quotient diagram, actual menus and their
positivity are instantiated from `CanonicalQuotientExpansion`. The
proved all-cycle bridge supplies a `CycleHom` for every real raw
expansion cycle from the original diagram's genuine specified cycle
premise. Universe transport applies the original CCO to that actual
expansion; completed readout preserves every quotient atomic edge.
Finite reindexing then exports the full interface on arbitrary finite
vertex types, in any universe. The empty vertex type is included.

Validation at this checkpoint: full root build, 1,011 jobs; explicit
`import CCO` checks for both source exports; official transitive audit
of 2,055 declarations with only `propext`, `Classical.choice`, `Quot.sound`;
artifact consistency check, 180 olean parts. No `sorry` or new axiom.
This discharges source C27. Literal C26 whole-two-path classification
and C28's complete assembled inheritance record remain separate gates.
