import CCO.RelationalCompletion.Relational.Source
import CCO.RelationalCompletion.Atomic.FanDiagram
import CCO.RelationalCompletion.Atomic.Fullness

/-! The TWO independent B038 source exports. The relational theorem uses
actual homogeneous age SAP and arbitrary finite-arity relational signatures.
The complete atomic theorem uses ordinary AP and locally allowed semantic CCO.
Neither theorem imports the assumptions or conclusion of the other. -/
namespace CCO.RelationalCompletion
export Relational.Structure
  (collision_unfolding collision_unfolding_source finite_family_unfolding already_injective)
export Atomic (triangleFullness)
end CCO.RelationalCompletion
