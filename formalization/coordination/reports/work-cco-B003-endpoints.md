# B003 C07 exact endpoint-survivor semantics

Proof checkpoint `63121dd7a36600bf61982fdff9a7f97545dc974b` on local
`takeover/b003-cyclehom`, extending the CycleHom/source-Helly checkpoint
`d2fcfea6ed513bc9b6286a9adf7be433d9790072`. All original project-2 history,
source pin `490c3f36d85db5a0b3ced0598e6c431825254ec5`, contracts, toolchain
and manifest are preserved. New implementation actor: `strong_bridge`.
This report does not create a claim or certify remote CI/integration.

## Proven source semantics

`ThetaFamilySemantics` constructs the actual finite typed private-word
diagram from a GIVEN family of literal original word lines over common
real roots. Its edge function records only genuine word adjacencies;
the label is their actual old source colour. Compatible duplicate
single-letter root edges therefore form ONE optional original atom.
There is no multigraph, artificial identity, or claimed fictitious 2-cycle.
Every original letter is proved to be precisely the diagram's edge, and
every homomorphism realizes all original words.

`ExactEndpointSemantics.thetaHomBetweenLiteralLines` proves that ANY other
literal common-root realizations of the SAME words define a homomorphism
of that SAME seed diagram. The proof uses exhaustive original forward or
conversed branch-letter witnesses, with their genuine original sort tags.
The diagram is not silently changed for a different surviving atom.

`present_atom_survives_theta_of_SAP` starts with any GIVEN diversity atom
of the presented menu. Original pair homogeneity aligns each word over a
real pair carrying that atom. The resulting common-root theta map can
collide at nonadjacent private vertices. Both real roots are already
distinct because their colour is the original diversity atom; accepted
SAP injectivization therefore pins BOTH roots and separates all vertices.
This proves that the prescribed atom survives in an actual injective
completion, including repeated original named sorts.

`theta_survivor_eq_present_of_SAP` gives literal equality with the
whole-diagram survivor set. Finally,
`exact_menu_survivor_representation_of_SAP` states that every original
nonempty `Exact` menu is precisely the survivor menu on two distinct roots
of one finite strongly completable private-word diagram; it also exports
whole-word readout. Empty restriction families mean typed diversity Top,
and compatible direct-letter repetitions are included.

These endpoint results use only original homogeneity plus SAP: a common
atom is GIVEN by the exact-menu nonemptiness hypothesis. They do not use
CCO, assume word Helly, or feed a presumed common atom into the separate
pairwise-to-total Helly proof. Together with the actual CycleHom bridge,
source WordHelly/exact-menu Helly, existing exact meets/converse, and the
source C08 consumers, this closes the C07/C08 provider and endpoint seams.

B003 remains **IN_PROGRESS**. C09 three-root sufficiency, C12 whole-graph
completion and simple-path formula, C13 canonical classification, and the
independent AP+CCO triangle-fullness proof are still open.

## Verification

All five new public modules occur in `CCO.lean`. Full local root build
succeeds with the exact pinned Lean4.34.1 and manifest: **1014 jobs**.
Transitive local audit of **1521 CCO declarations**, including private
names via `Lean.privateToUserName`, permits only `propext`,
`Classical.choice`, `Quot.sound`. The newly added modules emit no warnings.
Remote exact-head CI and genuinely non-author exact-SHA review remain
required before any submission or integration; no such result is invented.

The reproducible audit imports `CCO` and `Lean.Util.CollectAxioms`, then
iterates the environment constants whose user name has prefix `CCO` and
calls `Lean.collectAxioms` on each original declaration name. Every axiom
outside the three-name allowlist raises an error. `#print axioms` on the
CycleHom, source WordHelly and exact-product consumer separately confirms
the same allowlist. The precise source theorem statements are stored in
the five committed Lean files, not only in this report.
