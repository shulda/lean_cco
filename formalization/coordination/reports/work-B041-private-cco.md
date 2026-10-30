# B041 private paths and actual simultaneous quotient HOM CCO

Author: `/root/b041_simultaneous/private_cco`. Implementation lives only in
`CCO/SimultaneousQuotients/Private/` and `CCOBranch/`; the batch owner owns
root imports and the final submission. Mathematical source is the frozen
`490c3f36d85db5a0b3ced0598e6c431825254ec5`,
`sections/simultaneous_typed_exact_quotients.tex`, the private-path lemma and
the semantic-CCO branch of the simultaneous-quotient theorem. No source,
contract, toolchain, manifest or accepted API was changed.

## Public exports and exact scope

`CCO.SimultaneousQuotients.Private.Data n` has only a finite list of
positive path lengths over each unordered marked pair. It has no group,
source, exactness, homogeneity, SAP or CCO premise. Its formal vertices are
all marks and disjoint strict interiors; empty lists retain marks and add
no paths. `Data.whole_path`, `cycle_has_two_marks`, `cycle_classification`
and `projected_edge_has_path` prove the entire pure graph classification.
The two-mark branch has TWO DISTINCT WHOLE path occurrences, with equality
of both vertex and traversed-edge supports; the other branch has a genuine
injective marked cyclic order of length at least three and actual base
edges. `mark_injective`, `no_edges_of_empty` and `no_cycles_of_empty` cover
the retained isolated-mark/zero-path boundary.

The uncoloured graph uses one fixed explicitly constructed Nat structure
with ONE diversity colour purely as a `PartialDiagram` encoding. Every
positive length is realized at any two distinct Nat points (proved by
induction), so consistency is constructed, never assumed. These Nat points
are not formal vertices. This reuses the accepted B002 generic combinatorial
whole-path proof without importing an A01-like source premise into the new
source-free export. Coincident direct paths are one graph edge.

`CCO.SimultaneousQuotients.CCOBranch.semanticCCO` proves semantic HOM CCO
for arbitrary typed source/target universes and sort-preserving equivariant
surjective quotient maps with the actual full exact kernels and actual
old-group orbital language. These are representation inputs, not principal
cycle/Helly/CCO completion providers.

The source instance
`CCO.SimultaneousQuotients.canonical_semanticCCO S H cco J E represents`
has precisely the literal quotient carriers and actual orbital source
`ExactCRT.CanonicalTyped.source S H J E represents`. All maps, actions,
kernel identities and named orbital correspondence are instantiated by
accepted canonical constructors. Its finite-diagram vertex universe is
arbitrary; its conclusion is `SemanticCCO`, not injective completion.

## Claim map

| Claims | Actual Lean path |
|---|---|
| C11 | `Private.Graph`: Data's positive reduced lengths, disjoint formal interiors, simple graph encoding, `diagram_support`; equality-letter omission is the accepted `diversityLength`/`eraseEquality` normalization. |
| C12 | `Private.Data.whole_path`; underlying accepted generic `whole_path_on_cycle_of_interior` proves every position and edge. |
| C13 | `Private.Data.cycle_has_two_marks`. |
| C14-C17 | `Private.Data.cycle_classification`, `projected_edge_has_path`; underlying exact two-WHOLE-path and marked-simple-cycle supports retained. |
| C18 | `CCOBranch.Menus.atomExact_top_words` normalizes every top actual pullback to `[]`; `menus`, `project_completed` retain all marks and read the empty constraint vacuously. |
| C29 | `Menus.exact_atom_data`, `atomExact_represents`: accepted `ExactCRT.quotient_atom_pullback_exact` supplies the actual nonempty full exact original block. |
| C30 | `Menus.exact_atom_data` positive-word proof: zero length gives tagged OLD equality; sort-preserving projections give tagged QUOTIENT equality, contradicting the actual quotient diversity atom. |
| C31 | Accepted `QuotientExpansion.overlapping_edge_reference_colours`, `candidate_functional`, used by the generic constructed expansion: both direct restrictions use the same actual nonempty menu witness, hence the same genuine old atom. Identity-padded direct words are included. |
| C32 | Generic `QuotientExpansion.diagram`, its exact `diagram_support_iff` and the generated private menus. All marks remain even if their incident menus are empty. |
| C33 | `CCOBranch.all_raw_cycles_of_typed_cycles`, accepted generic `cycle_marked_cases` and full `cycle_two_whole_paths_or_marked_projection`. |
| C34 | `menus_realised_of_single_label` chooses one actual quotient edge witness; `menus_realised_of_marked_projection` uses ONE homomorphism of the ENTIRE genuine projected simple quotient cycle. |
| C35 | `Menus.menu_holds_of_actual_edge`, typed `cycleRealRepresentatives_project` and `menus_realised_of_marked_projection`. One old representative per displayed variable, with the original sort retained through dependent transport; all adjacent block constraints hold simultaneously. |
| C36 | `all_raw_cycles_of_typed_cycles` invokes accepted generic `cycleHom_of_marked_edge_realization`: independent actual word witnesses agree on marks and realize the entire raw cycle; real images need not be injective. |
| C37 | `CCOBranch.semanticCCO_fin`: applies ORIGINAL `semanticCCO_change_universe S cco` to the entire constructed finite original diagram. |
| C38 | `Menus.project_completed` invokes accepted whole-menu readout and `project_expansion_hom`; every listed word is recovered and top's list is vacuous. |
| C39 | `CCOBranch.semanticCCO` / `canonical_semanticCCO`: all finite vertex universes, all specified simple cycles, all specified quotient edges. |

The branch has no quotient homogeneity, AP/JEP, triangle fullness, SAP,
quotient word-Helly, quotient convolution, reverse descent or FullWord
criterion premise or inference. The accepted atomic-block exactness proof
is used as I02; it is not replaced by a new quotient Helly assumption.

## Local validation

Pinned Lean/Lake environment:
`source /workspace/scratch/6b2f11185e14/runtime/env.sh`.
Physical build slot was reused without moving the directory or deleting
accepted/generated output. The old B039 examples branch and commits are
preserved. Lake artifact restoration/cache remain disabled locally.

Final narrow command:

```
lake build CCO.SimultaneousQuotients.Private.Graph CCO.SimultaneousQuotients.CCOBranch.Semantics
```

Passed: 914 jobs in the dependency closure. All five new modules compile;
only normal pre-existing linter warnings and two optional `letI` style
warnings remain. No whole-project rebuild, audit, redundant controls or
new tests were run here; the batch owner and exact public CI provide the
final import closure, tests and transitive axiom audit. No open proof gaps
remain in this assigned branch.
