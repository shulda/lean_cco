import CCO.FullPhaseLift.Full.Separation
import CCO.FullPhaseLift.Equivariance.Inheritance
import CCO.FullPhaseLift.Tower.Elimination

/-! Optional A04, restricted to supplied natural STRICT pair targets,
is inherited by the SAME actually constructed selected full history.
No coherent action, natural target constructor or naturally colliding
completion equivalence is asserted. -/

universe v
namespace CCO.FullPhaseLift.Tower
open Canonical APCharacter APCharacter.Towers
noncomputable section
variable {M : Type v} [Countable M]

namespace SelectedStep
variable {A B : CurrentSource M} (s : SelectedStep A B)
include s

theorem separation (sep : Full.SeparatesPoints A.table) : Full.SeparatesPoints B.table := by
  rw [s.target]
  exact Full.separatesPoints_marked sep (SingleStep.mark A s.phase)

theorem optional (sep : Full.SeparatesPoints A.table)
    (optional : Equivariance.NaturalSupportNormal A.table) :
    Equivariance.NaturalSupportNormal B.table := by
  rw [s.target]
  apply Equivariance.naturalSupportNormal_of_fullIso (SingleStep.fullIso A s.phase)
  exact Equivariance.naturalSupportNormal A.table A.symmetric s.phase.masks
    (SingleStep.classSAP A s.phase) sep optional (SingleStep.oldIso A s.phase)
end SelectedStep

/-- The actual ordinary history suffices. The optional gate is an extra
INITIAL hypothesis and is constructed at every current successor. -/
theorem history_optional {A B : CurrentSource M} (h : History Next A B)
    (sep : Full.SeparatesPoints A.table)
    (optional : Equivariance.NaturalSupportNormal A.table) :
    Full.SeparatesPoints B.table ∧ Equivariance.NaturalSupportNormal B.table := by
  induction h with
  | nil A => exact ⟨sep,optional⟩
  | cons hs tail ih =>
    exact ih ((Classical.choice hs).separation sep) ((Classical.choice hs).optional sep optional)

end
end CCO.FullPhaseLift.Tower
