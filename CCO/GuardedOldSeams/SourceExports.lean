import CCO.GuardedOldSeams.LiftSource
import CCO.GuardedOldSeams.BranchEquation
import CCO.GuardedOldSeams.BranchSource
import CCO.GuardedOldSeams.OldSeams
import CCO.GuardedOldSeams.SeamBoundary
import CCO.GuardedOldSeams.EnvelopeMI
import CCO.GuardedOldSeams.IdempotentLattice
import CCO.GuardedOldSeams.IdempotentBoundary
import CCO.GuardedOldSeams.Simultaneous
import CCO.GuardedOldSeams.WordInsertionIdempotent
import CCO.GuardedOldSeams.WordInsertionBoundary

/-!
# Source15 exports and boundaries

The guarded lift below is the actual bounded-source construction in the
positive binary named signature. Its target can be finite and induced.
No assertion extends the binary local-cover proof to higher arities.

The OLD telescope requires literal source readouts. The direct raw word
square and its exact envelope use source homogeneity and visible SAP;
represented MI reconstruction and distributivity separately retain CCO.
The full idempotent/monolith branch retains the full relative-index gate.

The visibility formula uses the restored full pullback or its explicit
diversity guard. The printed unguarded RAW diversity equation is refuted.
All reinsertions keep the entire original positive word and a complete
old induced base, including every old cross-pair colour.
-/

namespace CCO.GuardedOldSeams.Source

export CCO.GuardedOldSeams
  (G_typ FiniteVisibleCompletion FiniteHiddenCompletion
   typed_guarded_lift_equivalence typed_guarded_finite_lift_equivalence
   typed_guarded_lift_canonical_HE typed_hidden_noncompletion_lifts G_typ_word_readback
   G_typ_all_root_equations G_typ_all_named_continuations
   old_seam_telescope old_seam_empty
   represented_word_square_envelope envelope_raw_exact
   idempotentEnvelopeIso originalMonolith leastIdempotent leastIdempotent_product
   represented_exact_mi_intersection_eq
   fullFactorPullback_sandwich fullFactorPullback_diversityGuard
   guardedFactorPullback_sandwich named_projection_raw_saturation_fails
   visible_source_kernel_le visible_target_kernel_le visible_branch_readouts
   old_branch_equation old_branch_atomic_equation
   guarded_old_branch_equation guarded_old_branch_atomic_equation
   branchAtomicTarget_eq_positiveBranchTarget
   word_insertion_over_complete_base idempotent_word_reinsertion
   simultaneous_word_insertion simultaneous_empty)

end CCO.GuardedOldSeams.Source
