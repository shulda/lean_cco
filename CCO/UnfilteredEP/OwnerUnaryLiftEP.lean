import CCO.UnfilteredEP.OwnerUnaryEP
import CCO.UnfilteredEP.UnaryEPComposition

/-! The independent pair-local unary EP is realized in the literal
existing UnaryLift language used by the final relational EP composition. -/

set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 250000
set_option maxHeartbeats 900000
universe u v w p
namespace CCO.UnfilteredEP
open CCO CCO.CloneTupleGeometry CCO.APCharacter CCO.APCharacter.Towers
open CCO.APRamseyReadout CCO.TerminalHiddenHN
noncomputable section
variable {B D : OwnerStage.{u,v,w}}

/-- Actual C89 interface: every genuine unfiltered unary competitor on
ONE old host contains the target, in the SAME unary-lift expansion. -/
theorem owner_unfiltered_unary_lift_EP
    (base : B.Sorts) (one : ∀ i : B.Sorts, base = i)
    (history : History OwnerStage.Next B D) (terminal : D.Terminal)
    (F : Charts.{u,v,w,p} D)
    (priority : LinearOrder (CoordinateLanguage D terminal).Sorts) :
    (UnaryLift.data (OwnerStage.historyReduct history) (unitReadoutData D.source)).EP := by
  let P := OwnerStage.historyReduct history
  let E := unitReadoutData D.source
  intro A a
  rcases a with ⟨table,L,a,rfl⟩
  obtain ⟨host,hHost⟩ := owner_unfiltered_unary_EP base one history terminal F priority
    A (reductMarkingOfLift P L)
  refine ⟨host,?_⟩
  intro b
  rcases b with ⟨table,M,b,rfl⟩
  obtain ⟨f⟩ := hHost (reductMarkingOfLift P M)
  let old := ownerEmbeddingToInduced B f.old
  let terminalMap := UnaryLift.embedding_of_sorts L M old f.labels
  let lifted : E.Embedding a b := {
    old := terminalMap
    unary_iff := fun R => PEmpty.elim R
    binary_iff := fun R => PEmpty.elim R }
  exact ⟨UnaryLift.toOldEmbedding P E L M lifted⟩

end
end CCO.UnfilteredEP
