import CCO.OldIdempotentForest.BoundedHidden
import CCO.OldIdempotentForest.CycleReconstructionSourceSimple
import CCO.OldIdempotentForest.PathReconstructionRequests
import CCO.OldIdempotentForest.SourceBoundaries
import CCO.OldIdempotentForest.ForestBoundaries
import CCO.OldIdempotentForest.PruningBoundaries

/-!
# Source16 exports and scope

The six binary source results use the actual reachable typed profiles,
the accepted finite-semigroup forest, literal OLD term equalities and the
original occurrence-indexed words. Every maximal deleted interval is kept
whole. The RAW idempotent envelope is used before diversity is extracted
at distinct actual representatives. All piece words and the separate fixed
original anchor share one complete old induced base.
The accepted SAP finalization chooses an injective realization of that
original cycle over the same base, fixes retained OLD generator pins and
preserves every original fine edge, with all unpinned positions fresh.

The final obstruction theorem assumes unary admissibility of the actual
original partial hidden structure. Its uniform bound depends only on the
fixed original language. The malformed total-unary boundary is explicitly
a two-transition reduct of the accepted common-block example; it is not a
new full original hidden-signature model. No higher-arity factor preservation
or completion theorem is asserted by these binary exports.
-/

namespace CCO.OldIdempotentForest.Source

export CCO.OldIdempotentForest
  (ReachableProfile TypedProfileState profileSemigroup profileEval
   positive_chain_nonzero positive_interval_nonzero nonzero_idempotent_profile
   composable_forest_subtree_nonzero composable_forest_common_child_profile
   MacroPath SupportedMacroSide SourceMacroPath SupportedMacroChain SourcePrunedForest
   sourcePrunedForest_exists old_gap_coordinate_equation
   old_gap_boundary_envelope old_gap_boundary_diversity_of_tagged
   source_reconstruction_requests_of_hom
   PathReconstructionRequests path_reconstruction_requests_of_hom
   source_macro_path_compression pruned_finite_completion_has_hom
   SupportedSpecifiedCycle supported_specified_cycle_exists
   exact_simple_cycle_over_complete_base
   typedObstructionBudget typed_bounded_hidden typed_bounded_hidden_uniform
   same_idempotent_profile_different_original_words
   forest_envelope_not_finer forest_envelope_restores_identity
   forest_fixed_anchor_not_forced forest_commonBlock_unbounded_malformed
   forest_singleton_boundary forest_source_exact_disjoint_payload)

export CCO.OldIdempotentForest.MacroPath
  (exists_factorization_forest_sharp exists_factorization_forest)

export CCO.OldIdempotentForest.SourcePrunedForest
  (gap_original_idempotent gap_old_coordinate_certificates
   retained_bounds oldGenerators oldGenerators_card piece_old_boundaries
   gap_boundary_original_profile old_anchor_bound)

export CCO.OldIdempotentForest.SupportedSpecifiedCycle
  (reconstruct_cycle_hom retainedPins reconstructionPoint
   reconstruct_simple_cycle reconstructed_retained_image)

export CCO.OldIdempotentForest.PathReconstructionRequests
  (whole_original_path reconstruct_macro_path)

export CCO.OldIdempotentForest.Prunes
  (exact_partition located_slice exact_original_payload uniform_bounds
   located_gap_idempotent)

end CCO.OldIdempotentForest.Source
