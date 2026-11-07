import CCO.UnfilteredEP.NormalizedReadoutRamsey
import CCO.UnfilteredEP.OwnerUnaryLiftEP

/-! Final same-history composition interface for the concrete normalized
hidden class. Its hidden class, Ramsey and EP inputs remain explicit
until the actual synchronized hierarchy supplies them. -/

universe u v w p
namespace CCO.UnfilteredEP
open CCO CCO.FullCode CCO.APRamseyReadout CCO.CloneTupleGeometry
open CCO.APCharacter.Towers CCO.TerminalHiddenHN
noncomputable section
variable {B D : OwnerStage.{u,v,w}}
variable (history : History OwnerStage.Next B D) (terminal : D.Terminal)
variable (F : Charts.{u,v,w,p} D)
variable (ages : ExpansionAges.{max u v w,max u v} (coordinateOrderExpansion D terminal).toReduct)
variable (oldAge : ∀ C, ages.oldAge C ↔ ProperFiniteCodeAge D terminal C)
variable (proper : ∀ C, ages.expandedAge C → ProperOrderedAge D terminal C)

/-- Every actual terminal tag and every FULL normalized code is retained
over the SAME arbitrary supplied genuine history. -/
def ownerNormalizedReadoutData : RealExpansionData B.source :=
  UnaryLift.data (OwnerStage.historyReduct history)
    (normalizedReadoutData D terminal F ages oldAge proper)

/-- Combining the actual unary EP with the actual normalized hidden EP
chooses one original host before every full competing expansion. -/
theorem owner_normalized_full_expansion
    (base : B.Sorts) (one : ∀ i : B.Sorts, base = i)
    (priority : LinearOrder (CoordinateLanguage D terminal).Sorts)
    (ramsey : HasHiddenRamsey ages.expandedAge) (hiddenEP : ages.HiddenEP) :
    (ownerNormalizedReadoutData history terminal F ages oldAge proper).Reasonable ∧
      (ownerNormalizedReadoutData history terminal F ages oldAge proper).Ramsey ∧
      (ownerNormalizedReadoutData history terminal F ages oldAge proper).EP ∧
      (∀ A, Finite ((ownerNormalizedReadoutData history terminal F ages oldAge proper).Expansion A)) := by
  refine ⟨?_,?_,?_,?_⟩
  · exact UnaryLift.reasonable (OwnerStage.historyReduct history)
      (normalizedReadoutData D terminal F ages oldAge proper)
      (OwnerStage.historyTransition history).reasonable
      (normalized_readout_data_reasonable D terminal F ages oldAge proper)
  · exact UnaryLift.ramsey (OwnerStage.historyReduct history)
      (normalizedReadoutData D terminal F ages oldAge proper)
      (normalized_readout_data_ramsey D terminal F ages oldAge proper ramsey)
  · exact unaryLift_EP (OwnerStage.historyReduct history)
      (normalizedReadoutData D terminal F ages oldAge proper)
      (owner_unfiltered_unary_lift_EP base one history terminal F priority)
      (normalized_readout_data_EP D terminal F ages oldAge proper hiddenEP)
  · exact (ownerNormalizedReadoutData history terminal F ages oldAge proper).finite_expansions

end
end CCO.UnfilteredEP
