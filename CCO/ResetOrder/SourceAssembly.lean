import CCO.ResetOrder.SortRestriction
import CCO.ResetOrder.Normalization
import CCO.ResetOrder.Hierarchy.Consumer
import CCO.ResetOrder.ResetSetting
import CCO.ResetOrder.FiniteTower
import CCO.ResetOrder.ClosureBoundaries
import CCO.ResetOrder.Counterexample.Consumer
import CCO.ResetOrder.Unary.Definable

/-! B036: six scoped source exports, with concrete provider proofs.
The hierarchy synchronizes FIBRE tasks, and composition retains its actual
closed-restriction gate. No unrestricted added-function composition or global
transition monotonicity is exported. -/
namespace CCO.ResetOrder

export Unary (restriction_ramsey restricted_hereditary restriction_jep restriction_sap
  abstract_reset_order_EP fresh_midpoint_from_ordered_sap)
export Generic.Normalizer (foundational_ramsey_normalization)
export Hierarchy (hierarchical_order_normalization)
export Generic (foundational_relative_EP_composition relation_only_relative_EP_composition
  relativeEP_finite_tower relation_only_relativeEP_finite_tower)
export Counterexample (C54_all_sizes upper_not_reasonable)
export ClosureBoundaries (no_actual_pointed_generated_embedding)

end CCO.ResetOrder
