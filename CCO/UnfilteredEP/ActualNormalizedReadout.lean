import CCO.UnfilteredEP.NormalizedExpansionAges
import CCO.UnfilteredEP.OwnerNormalizedExpansion

/-! Actual normalized finite relational data. All age fields and Ramsey
providers are discharged at the same terminal source. The remaining
relative order EP theorem is named explicitly in the EP interfaces. -/

universe u v w p
namespace CCO.UnfilteredEP
open CCO CCO.FullCode CCO.APRamseyReadout CCO.CloneTupleGeometry
open CCO.APCharacter.Towers CCO.TerminalHiddenHN
noncomputable section
variable (D : OwnerStage.{u,v,w}) (terminal : D.Terminal) (F : Charts.{u,v,w,p} D)
variable (priority : LinearOrder (CoordinateLanguage D terminal).Sorts)

abbrev actualNormalizedReadoutData :=
  normalizedReadoutData D terminal F (actualNormalizedExpansionAges D terminal priority)
    (actual_normalized_old_age D terminal priority)
    (actual_normalized_expanded_proper D terminal priority)

theorem actual_normalized_readout_reasonable :
    (actualNormalizedReadoutData D terminal F priority).Reasonable :=
  normalized_readout_data_reasonable D terminal F _ _ _

theorem actual_normalized_readout_ramsey :
    (actualNormalizedReadoutData D terminal F priority).Ramsey :=
  normalized_readout_data_ramsey D terminal F _ _ _
    (actual_normalized_hidden_ramsey D terminal priority)

theorem actual_normalized_readout_EP
    (hiddenEP : (actualNormalizedExpansionAges D terminal priority).HiddenEP) :
    (actualNormalizedReadoutData D terminal F priority).EP :=
  normalized_readout_data_EP D terminal F _ _ _ hiddenEP

variable {B : OwnerStage.{u,v,w}} (history : History OwnerStage.Next B D)

abbrev actualOwnerNormalizedData :=
  UnaryLift.data (OwnerStage.historyReduct history)
    (actualNormalizedReadoutData D terminal F priority)

/-- Everything except the standalone concrete relative order EP is
discharged for the SAME specified genuine history and every terminal tag. -/
theorem owner_actual_normalized_expansion_of_hidden_EP
    (base : B.Sorts) (one : ∀ i : B.Sorts, base = i)
    (hiddenEP : (actualNormalizedExpansionAges D terminal priority).HiddenEP) :
    (actualOwnerNormalizedData D terminal F priority history).Reasonable ∧
      (actualOwnerNormalizedData D terminal F priority history).Ramsey ∧
      (actualOwnerNormalizedData D terminal F priority history).EP ∧
      (∀ A, Finite ((actualOwnerNormalizedData D terminal F priority history).Expansion A)) :=
  owner_normalized_full_expansion history terminal F
    (actualNormalizedExpansionAges D terminal priority)
    (actual_normalized_old_age D terminal priority)
    (actual_normalized_expanded_proper D terminal priority)
    base one priority (actual_normalized_hidden_ramsey D terminal priority) hiddenEP

end
end CCO.UnfilteredEP
