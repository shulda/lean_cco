# B047 old SAP infinitude and finite witness assembly

Actual author: `/root/b047_pair_safe_split/infinite_type_fibres`.
Source pin: `490c3f36d85db5a0b3ced0598e6c431825254ec5`.
Read pair_safe_split C22–C28/N05 and its actual source contract. The new
namespace is `CCO.PairSafeSplit.Infinity`; file names are module locations.

`TypeFibres.lean` proves `finite_invariant_subset_base` directly from the
accepted original age-SAP infinite-stabilizer-orbit theorem. Every finite
real set invariant under the actual pointwise stabilizer of its finite
parameter base lies inside that base. This is a semantic statement with
the invariance proof displayed, not a definability or algebraicity oracle.

`typeFibre` is the literal complete one-point finite qf type, including
the sort/diagonal and BOTH full oriented spoke colours to each real base
point. `typeFibre_iff_orbit` proves exact equality with the old stabilizer
orbit by actual finite tuple homogeneity. `typeFibre_avoids`,
`typeFibre_motion` and `typeFibre_infinite` retain off-base inequalities,
pointwise parameters and all actual original sorts.

For ANY actual colour-invariant equivalence strictly above equality,
`class_has_other` and `equivalence_class_infinite` prove that every real
class is nontrivial and infinite. `type_class_infinite` is the central
type/gate intersection proof: if that intersection were finite, choose
an anchor y in the infinite gate class outside the finite intersection
and the old base. Its stabilizer together with the old base preserves
the finite intersection and moves an off-base x inside it, contradicting
`finite_invariant_subset_base`. No new-source SAP, CCO, countability,
exactness, marking homogeneity or generic quotient-SAP transfer is used.

`MarkedFibres.lean` proves `markedTypeFibre_infinite` for ANY fixed marking
constant on the actual gate classes. The marking is never assumed
homogeneous. The inactive case is `constant_markedTypeFibre_infinite`.
`exists_marked_witnesses` supplies distinct actual Fin n witnesses.

`OldWitnesses.lean` supplies the requested independent C30 assembly
support. `tupleBase` deletes exactly the original anchor slot, and
`exists_old_witnesses` injectively extends the WHOLE original tuple by
arbitrarily many distinct actual same-type, same-mark points outside its
entire finite range. `replacePoint_colours` preserves EVERY ordered full
old colour, including diagonal entries; `replacePoint_marks` preserves
the actual unary marking and `replacePoint_injective` proves genuine
induced tuple injectivity for the fresh replacement. Its infinitude input
is a local support lemma which the owner instantiates from the preceding
old-SAP theorems, not a final source-provider premise.

Actual maximal/reached-gate nontriviality C24, its source instances and the
Fraisse-limit transport/C31–C32 actual marked SAP are owned by the parent.
This helper does not claim that those assembly obligations are complete.

Pinned local Lean 4.34.1, bundled Lake and unchanged manifest:
`lake build CCO.PairSafeSplit.Infinity.OldWitnesses` passed 998 jobs.
Only scoped incremental consumers were built; no broad test/audit suite
or reviewer compilation was run. Source, accepted APIs and pins remain
unchanged. Worktree cco-b047-infinity has private build/provider outputs;
no other worker's files, original branches or untracked copies were changed.
