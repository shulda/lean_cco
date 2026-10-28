# Independent review: B003 exact endpoint semantics

Reviewer `/root/independent_review` authored none of this implementation or
original project-2 code. This is a source checkpoint review, not approval of
the entire B003 package. Source pin remains
`490c3f36d85db5a0b3ced0598e6c431825254ec5`.

Reviewed exact local checkpoint:
`5e41026af1b5b2d777675204bbe63c135b4ac3be`, production proof
`63121dd7a36600bf61982fdff9a7f97545dc974b`. I also compared successor
`56c6d555f6adce30894a8b64cdf754ac3c09e0db`: it merges the already reviewed
policy main `97211488e4ac166a4b0650953363a0c3cb7614f5` and changes no Lean
file relative to the endpoint checkpoint.

**Disposition: exact source checkpoint approved.** I independently fetched
public PR4 head555951c6a4c51d0842252fdebc142e422127788f and verified tree
8868a6b69561d686b024680702e17593e1a2bfa3 equals reviewed local56c6d555.
Run40680013056/job122788040064 passes48tests,1014buildjobs and audit1521
with only the standard three axioms. The synthetic CI merge
07da647f03084751739da7c5b2680415192dcdbd has that identical tree, independently
confirmed from its remote Git object. Complete package review remains
separate; this green partial checkpoint stays IN_PROGRESS.

I read both additive modules ThetaFamilySemantics and ExactEndpointSemantics,
the root imports, current source map, the existing literal-word/readout,
actual survivor and fixed-root SAP signatures, and the pinned C07 source.

A GIVEN common atom realizes each word over the same actual endpoint pair.
The seed diagram records only genuine private-word adjacencies, with their
actual original colours. Duplicate direct branches therefore impose one
optional atom rather than parallel edges or a fictitious 2-cycle. Every
forward word letter is proved equal to that diagram label, and arbitrary
diagram homomorphisms read back the complete original word.

The crucial quantifier is preserved: EVERY atom of the presented exact menu
survives in the SAME seed diagram. The theorem does not change diagrams
for different atoms. Its alternate literal lines preserve every seed edge
by exhaustive original forward/converse branch-letter witnesses. The
injectivization pins both real roots only after the given actual diversity
atom proves their images distinct; repeated named sorts and collisions of
nonadjacent initial private vertices are permitted.

The survivor equality includes empty restriction lists (typed diversity Top)
and compatible duplicate direct letters. The final representation theorem
constructs a finite strongly completable diagram for every nonempty original
Exact menu and exports whole-word readout. These endpoint results use
original homogeneity plus SAP, with no CCO or WordHelly premise: existence
of the seed atom follows from the GIVEN exact-menu nonemptiness, so it is
not used circularly to prove the separate pairwise-to-total Helly theorem.
Together with the previously reviewed CycleHom/provider/Helly chain and
source C08 consumers, this closes the C07 endpoint seam.

I independently reran the full 1014-job local root build and the official
axiom-audit v0.1.2 pinned at
`46024e005996495c65ef609368e11ab39c4222e3`. All 1521 CCO declarations pass
with only propext, Classical.choice and Quot.sound. Both new public modules
are imported from CCO.lean. The pinned Lean 4.34.1/manifest and documented
local executable-discovery shim are unchanged.

C09 three-root sufficiency, C12 whole-graph completion/simple-path identity,
C13 canonical PC classification and independent AP+CCO triangle fullness
remain open in this checkpoint. B003 stays IN_PROGRESS; no submitted or
accepted dependency, integration or remote CI result is asserted here.
