import CCO.UnfilteredEP.OwnerTemplateProviderArrows

/-! Same-map reasonableness of the actual pair-local unary age and its
FULL block-code provider, along the literal given genuine history. -/

set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 250000
set_option maxHeartbeats 900000
universe u v w p
namespace CCO.UnfilteredEP
open CCO CCO.CloneTupleGeometry CCO.APCharacter CCO.APCharacter.Towers
open CCO.APRamseyReadout CCO.TerminalHiddenHN
noncomputable section

/-- The proposed joint marking extends along the SAME old map. Actual
whole-history realization and genuine unary reasonableness supply it. -/
theorem owner_template_reasonable {B D : OwnerStage.{u,v,w}}
    (history : History OwnerStage.Next B D) :
    (ownerFiniteAge B).Reasonable (ownerTemplate history) := by
  intro A E f a
  obtain ⟨L,hL⟩ := owner_marking_lift history A a
  let old := ownerEmbeddingToInduced B f
  obtain ⟨M,g,hg⟩ := UnaryLift.lift_reasonable (OwnerStage.historyReduct history)
    (OwnerStage.historyTransition history).reasonable L old
  refine ⟨reductMarkingOfLift (OwnerStage.historyReduct history) M,?_⟩
  intro x
  have hs := g.preserves_sort (L.toObject x)
  rw [hg x] at hs
  exact hs.trans (hL x)

/-- The full block relational expansion over the original source retains
literal reasonableness from both proved stages. -/
theorem owner_lifted_block_reasonable {B D : OwnerStage.{u,v,w}}
    (history : History OwnerStage.Next B D) (terminal : D.Terminal)
    (F : Charts.{u,v,w,p} D)
    (priority : LinearOrder (CoordinateLanguage D terminal).Sorts) :
    (ownerLiftedBlockData history terminal F priority).Reasonable :=
  UnaryLift.reasonable (OwnerStage.historyReduct history)
    (actualFullBlockReadoutData D terminal F priority)
    (OwnerStage.historyTransition history).reasonable
    (actual_full_block_readout_reasonable D terminal F priority)

end
end CCO.UnfilteredEP
