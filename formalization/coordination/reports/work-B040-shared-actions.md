# B040 shared action support consumers

Actual author: `/root/b040_transport/shared_actions`.
Branch: `work/B040-shared-actions`; base is accepted main
`90feb040df23e2ef7fd18ebc7df3b92ccfc0a8a0`.
Source pin: `490c3f36d85db5a0b3ced0598e6c431825254ec5`,
`sections/typed_invariant_quotient_transport.tex`, unchanged blob
`3895b17d7d0176a74d6f69c39e4e22d9cdba5715`.

These three modules document and consume the already shared B001 action
API. `CCO/GroupActions.lean`, `CCO/GroupQuotient.lean`, their exports,
receiving ownership and every existing consumer import are unchanged.
There is no mathematical import from any later package. The finite C4/C2
boundary is proved directly from targeted Mathlib modules here.

All new declarations are in `CCO.QuotientTransport.SharedActions` and its
`NonfaithfulNonsplit` or `PointHypotheses` subnamespaces.

| Claims | Actual Lean discharge |
|---|---|
| C27 | `lifted_point_same_fibre`: an arbitrary lift of the literal requested group element lands in the actual requested fibre. |
| C28 | `left_kernel_correction`: the correcting kernel element is multiplied on the left. |
| C29 | `onto_of_all_requests`: nonempty Y and onto π force onto ρ from every compatible request. |
| C30 | `kernel_transitive_of_all_requests`: γ=1 gives actual kernel-fibre transitivity. |
| C31 | `shared_point_lifting_consumer` applies the existing B001 iff with precisely nonempty Y, onto π and equivariance. No faithfulness, transitivity or section premise. |
| C32 | `NonfaithfulNonsplit.nonfaithful_nonsplit_requests`: exact original Y=B=C2, π=id, C4 acts via reduction. The element 2 is nonidentity and fixes every point; every requested element lifts; no homomorphic section exists. The obstruction quantifies over all sections. |
| C33 | `kernel_equivalence_invariant`, `output_orbital_has_root_witness`, `output_orbital_pullback_invariant`: actual kernels, actual preimages and one original group action. |
| C34–C35 | `saturation_of_any_root_witness`: literal full `P_Θ=ker τ;O;ker σ` for every root witness, using existing B001 orbital saturation. Equality is retained. |
| C36 | `root_orbital_image_exact`: the image of the whole root orbital is exactly one output orbital. `diversity_pullbacks_partition` and `root_orbital_unique_diversity_part` prove cover and equality on overlap for actual points and actual root orbitals. |
| C37 | `diversity_saturation_of_witness`: restriction to D occurs after full saturation. The partition statements allow the actual tagged real-diversity predicate. |
| C38 | `disjoint_roots_diversity_nonempty`, `empty_typed_diversity_forces_same_sort`: different original sort indices give distinct tagged roots and exclude an empty diversity part. |
| C39–C40 | `nonidentity_kernel_mate_everywhere` derives a distinct kernel mate in every fibre from one identification and actual root transitivity. Existing B001 `no_diversity_injective` discharges both identity-kernel conclusions in `same_root_empty_diversity_iff`. |
| C41–C43 | `same_root_empty_diversity_iff` gives the exact same-root iff for arbitrary output representatives: both maps bijective and Θ the same-root graph. Q and R remain independent types. `graph_pullback_identity` proves full preimage literally identity; `empty_diversity_orbital_unique` proves at most one exception. Kernel identity iff injectivity is already the unchanged B001 theorem. |
| C44 | The preceding consumers cover both complete shared source results without reallocating either receiving export. No SAP, CCO, exactness, homogeneity or word-realization provider is used. |
| C48 | `diagonal_orbital_saturation_boundary` uses an actual diagonal root orbital; constant-map saturation contains distinct roots while prefiltering makes it empty. `diversity_orbital_saturates_diagonal` uses an actual off-diagonal root orbital and proves saturation adds a real diagonal pair. |
| C49 | `PointHypotheses.empty_domain_requests`, `nononto_point_map_requests`, `onto_without_kernel_transitivity` prove the three actual failures; their corresponding projections have explicit equivariance certificates. `point_motion_does_not_prescribe_group_element` separately shows why a nonfaithful target action cannot replace the prescribed group element by its induced point permutation. |

Local validation uses the pinned Lean 4.34.1 (commit
`5045d0056413266e57c625dcd7c365b10e377c52`) and unchanged manifest,
with the existing process-path shim and both Lake artifact restoration
switches false. The final narrow command is:

```text
source /workspace/scratch/6b2f11185e14/runtime/env.sh
lake build CCO.QuotientTransport.SharedActions.Boundaries
```

It compiles all three new modules and their dependencies. No whole-project
build, provider rebuild, axiom audit or external CI is claimed by this helper;
the batch owner and publisher retain those gates. No unresolved mathematical
provider remains in the claims assigned to this helper.
