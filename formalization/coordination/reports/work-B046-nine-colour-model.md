# B046 — actual nine-colour model and the two explicit good prefixes

Author: `/root/b046_orbital_cover/nine_colour_model`. The separate actual
author `/root/b046_orbital_cover/nine_colour_model/coordinate_potentials`
implemented the signed-potential, prescribed-phase, product and profile
modules; its report is `work-B046-coordinate-potentials.md`. Neither author
is a nonauthor reviewer. Parent owns the parity/Hasse and diagonal-cover/AP
obstruction consumers. Frozen mathematical source remains
`490c3f36d85db5a0b3ced0598e6c431825254ec5`, selected proof in
`sections/v27/06_legacy_finite_covers.tex`, and the released B046 contract.

## Actual source and hypotheses

All names below are relative to `CCO.OrbitalCover.Example` unless qualified.
`Point` has the literal fields `u v n : Nat` and `p q : ZMod 2`. The model
uses three actual countably infinite pure sets; Nat is the chosen concrete
copy. `Core.lean` defines the singleton-sort AtomicSource `source`.
Every one of its nine diversity colours actually occurs; distinct clones
of one owner have diversity `(some 0,some 0)`, whereas original logical
equality has outer `none`. These are never identified.

`Aut` is the full group of all original colour-preserving point
permutations. Finite homogeneity is constructed by independent block
permutations, bit translations on each old block, and clone permutations
on each old owner. Repeated finite tuple values are retained. The stronger
`finite_extension_controlled` additionally sets chosen p/q translations
to zero on every block, including unused blocks, so the resulting whole
automorphism fixes the chosen literal predicates everywhere.

`strongAmalgamation` uses ordinary finite homogeneous alignment, then
keeps every owner and every designated base point while moving each
off-base clone index beyond the finite right/base index bound. The legs
have exactly the prescribed base as their intersection. This proves
unbounded actual AgeSAP; no finite diagnostic window is substituted.

## Source claim map

| Claims | Actual declarations and construction |
|---|---|
| C12; D04–D05 | `Point`, `coordinateColour`, `pattern`, `colour`, `source`, `colour_card`; actual nine-colour witnesses and original diagonal recognition. |
| C13–C14 | `coordinates_of_colour_eq`, `coordinatePerm`, `ownerFibrePerm`, `motionPerm`, `finite_extension`, `homogeneous`; full original language finite partial isomorphisms extend. |
| C15 | `freshen`, `freshen_injective`, `freshen_colour`, `freshen_mem_right`, `strongAmalgamation`; actual infinite clone freshness over the whole real designated base. |
| C16 | `coordinate_triple`, `coordTriangle_realized`, `triangle_iff`; explicit independent coordinate triples combine with clone indices 0,1,2, so the STRONG table has genuine three-distinct-point witnesses. |
| C17 | `coordinate_triangle_defined`; a complete one-coordinate table with exactly the displayed triangle law has a simultaneous block/bit realization, including empty/singleton/pair inputs. |
| C18 | `triangle_defined`; actual permitted complete diagrams embed inducedly in the original source. |
| C19–C22 | `Potentials.optional_phase_labels`, `Potentials.coordinate_blocks`, `Potentials.coordinate_solution`, `semanticCCO_injective`, `semanticCCO`; genuine specified old simple cycles force signed e-component consistency and forbid any n edge inside an e-component. Every component receives a fresh actual block; the two independent coordinate solutions combine with distinct original clone indices. |
| C23–C24 | `product_boxes`, `CoordProfile`, `positive_profile_box`, `positive_profile_nonempty`, `every_coordProfile_reachable`, `positive_profiles_helly`; actual positive-word profiles, not an uninstantiated recurrence. |
| C27 support | `diagonal_not_box`, `diagonal_not_positive_profile`; the actual coarse diagonal palette is not any positive STRONG word profile. Parent identifies the cover's palette with this literal set. |
| C38 | `Prefix.source`, `Prefix.homogeneous`, `Prefix.strongAmalgamation`; actual p, then (p,q) unary refinements, whole labelled-source homogeneity and real SAP. |
| C39 | `realize_prescribed`, `Prefix.oldDiagram`, `Prefix.old_cycle_hom`, `Prefix.atom_p`, `Prefix.atom_q`, `Prefix.semanticCCO`, `Prefix.triangle_defined`; actual whole diagram solutions retain the exact original prescribed phase values. |
| C40 support | `actual_model`, `Prefix.actual_prefix`; original and both good prefix source properties are instantiated, rather than assumed. Parent combines with the every-orientation AP obstruction. |

Triangle-definedness is deduced from the already constructed actual
coordinate CCO and actual finite homogeneity by the accepted ordinary-AP
triangle-fan theorem. Its direction is CCO to completion of complete
triangle-legal inputs. No converse from a multiplication table or a Helly
calculation to CCO is used. In particular `coordinate_triangle_defined`
embeds a one-coordinate input into a complete literal nine-colour input
with a constant second coordinate, then reads the constructed realization.

## Literal successful unary prefixes

`Prefix.Stage.first` names p; `Prefix.Stage.both` names (p,q). Their sorts
are all actual valid labels. Carriers are literal subtypes of the SAME
original `Point`, not new Fraisse-limit points. The accepted generic
`APCharacter.Rank.source` is used only as a constructor of these unary
refinements and of their actual occurring-colour subtypes. No character
mask, marked completion, identification, progress or later safe-splitting
theorem is imported as a premise or used to prove the model properties.

`Prefix.oldEquiv` is the actual global carrier bijection back to original
points. `Prefix.forgetSecondEquiv`, `Prefix.forgetSecond_literal`, `Prefix.reduct_same_point`
exhibit the second prefix as the literal further q refinement of the
first p refinement, with the original global reduct retained. The group
`Prefix.FullGroup` is the full original colour automorphism group restricted
to permutations fixing the chosen phase predicates globally. Tuple
homogeneity extends with one member of this whole group, not independent
unrelated actions on individual child sorts.

In the CCO proof, every local signed requirement is derived from an
actually occurring child colour. The inherited actual simple-cycle
homomorphisms are read in the original source; the direct potential solver
then keeps the prescribed p and, at the second stage, q functions exactly.
Neither a global extension provider nor arbitrary phase coherence is a
caller assumption. Strong amalgamation keeps these literal named labels
because its freshening changes only clone indices.

## Compilation and preservation

Pinned Lean 4.34.1, bundled Lake, unchanged manifest. Narrow incremental
targets compiled in private physical worktree `cco-b039-sap`, branch
`work/B046-nine-colour-model`. Intermediate successful targets include
Core (1146 jobs), original Homogeneity (1168), actual SAP (1169), prefix
CCO (1211), prefix SAP (1212), and final Model union (1264). Only new
incremental source targets were built; no duplicate whole-root/test/audit
pipeline was run here. Parent owns the assembled root build and remote
exact-head/main CI and transitive axiom audit.

All original B044 branches remain preserved. A transient physical-slot
collision with the B045 CCO helper was detected before any commit or
tracked-source loss: Core's exact bytes were preserved separately, the
other helper moved to its own isolated worktree, and only then did this
worker resume its original B046 branch. Other helper-owned untracked
material was not staged, cleaned or deleted. This worker writes only its
scoped new source modules and this report. All mathematical hypotheses,
accepted APIs, toolchain, external pins and source contracts are unchanged.
