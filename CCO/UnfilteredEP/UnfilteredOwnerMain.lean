import CCO.UnfilteredEP.ActualHiddenEP
import CCO.UnfilteredEP.ActualNormalizedReadout
import CCO.UnfilteredEP.ActualTupleContracts

/-! The actual unfiltered terminal source theorem. The specified genuine
history is never replaced, every terminal tag remains, and one old host
precedes every competing full relational expansion. -/

universe u v w p a
namespace CCO.UnfilteredEP
open CCO CCO.FullCode CCO.APRamseyReadout CCO.CloneTupleGeometry
open CCO.APCharacter.Towers CCO.TerminalHiddenHN
noncomputable section

variable (D : OwnerStage.{u,v,w}) (terminal : D.Terminal)
variable (F : Charts.{u,v,w,p} D)
variable (priority : LinearOrder (CoordinateLanguage D terminal).Sorts)

/-- All four finite-tuple transfer contracts hold at the SAME actual
synchronized hidden class. Its EP is the concrete reset-task theorem. -/
theorem actual_normalized_full_code_EP :
    VisibleFullCodeEP.{max u v w,max u v,a}
      (coordinateOrderExpansion D terminal)
      (actualNormalizedExpansionAges D terminal priority)
      (binaryNormalForms (cloneSource D) (cloneHomogeneous D) (cloneSAP D) (fullCovers D terminal))
      (orderedNormalForms (cloneSource D) (cloneHomogeneous D) (cloneSAP D) (fullCovers D terminal))
      (tupleScheme D terminal F) :=
  actual_root_covered_order_code_EP D terminal F
    (actualNormalizedExpansionAges D terminal priority)
    (actual_normalized_old_age D terminal priority)
    (actual_normalized_hidden_EP D terminal priority)

/-- C95 for ANY supplied genuine owner history. All source, pair-local,
core, singleton Ramsey, hierarchy, reset and SAME-host transfer gates
have been concretely discharged; no core filtering is performed. -/
theorem genuine_owner_unfiltered_expansion
    {B : OwnerStage.{u,v,w}}
    (base : B.Sorts) (one : ∀ i : B.Sorts, base = i)
    (history : History OwnerStage.Next B D) :
    (actualOwnerNormalizedData D terminal F priority history).Reasonable ∧
      (actualOwnerNormalizedData D terminal F priority history).Ramsey ∧
      (actualOwnerNormalizedData D terminal F priority history).EP ∧
      (∀ A, Finite ((actualOwnerNormalizedData D terminal F priority history).Expansion A)) :=
  owner_actual_normalized_expansion_of_hidden_EP D terminal F priority history base one
    (actual_normalized_hidden_EP D terminal priority)

end
end CCO.UnfilteredEP
