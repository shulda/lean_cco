import CCO.AutomaticEPCore.CodedTowerReceiving
import CCO.AutomaticEPCore.NamedIsoQuotient
import CCO.ExactEPGeometry.OriginalQuotientTower

/-! Quotient closure for the actual receiving category: source renamings
are erased by whole fixed-code quotient isomorphisms; each splitting step
uses its genuine B062 retained/discarded phase theorem. -/

universe u v w t
namespace CCO.AutomaticEPCore.IsoGateTower
open CCO.APCharacter.Towers CCO.ExactEPGeometry Classical
noncomputable section

variable (A : CurrentSource.{u,v,w,t}) (base : A.Sorts)
variable (hOne : ∀ i : A.Sorts, base = i)

def stepGate {s next : CertifiedGateTower.ExactPrefix A} (step : Step s next) :
    Option (ExactEq A.source base) :=
  match Classical.choice step with
  | .rename _ _ => none
  | .split actual => some (certifiedStepOriginalGate A base hOne actual)

def gates : {s next : CertifiedGateTower.ExactPrefix A} →
    History Step s next → List (ExactEq A.source base)
  | _, _, .nil _ => []
  | _, _, .cons step tail =>
    (stepGate A base hOne step).toList ++ gates tail

theorem gates_cons {s mid next : CertifiedGateTower.ExactPrefix A}
    (step : Step s mid) (tail : History Step mid next) :
    gates A base hOne (.cons step tail) =
      (stepGate A base hOne step).toList ++ gates A base hOne tail := rfl

/-- The quotient history is constructed for EVERY actual receiving
history, including arbitrary whole source renamings and zero steps.
Its exact count is the count of original gates containing E. -/
theorem quotient_safe_history
    (E : ExactEq A.source base)
    {s next : CertifiedGateTower.ExactPrefix A}
    (history : History Step s next) :
    ∃ projected : History CodedSafeSourceStep
      (codedSourceClass (originalCodedQuotient A base hOne E s))
      (codedSourceClass (originalCodedQuotient A base hOne E next)),
      projected.length = (gates A base hOne history).countP (fun G => decide (E ≤ G)) := by
  induction history with
  | nil s => exact ⟨.nil _,rfl⟩
  | @cons s mid next step tail ih =>
    obtain ⟨projected,hCount⟩ := ih
    cases chosen : Classical.choice step with
    | rename I =>
      have classes := (codedSourceClass_eq
        (namedIsoOriginalCodedQuotientIso A base hOne E s I)).symm
      rw [classes]
      refine ⟨projected,?_⟩
      simpa only [gates_cons,stepGate,chosen,Option.toList_none,List.nil_append] using hCount
    | split actual =>
      by_cases retained : E ≤ certifiedStepOriginalGate A base hOne actual
      · refine ⟨.cons (originalCodedQuotient_retainedStep
          A base hOne E actual retained) projected,?_⟩
        simp [History.length,gates_cons,stepGate,chosen,retained,hCount]
      · have classes := originalCodedQuotient_discardedStep A base hOne E actual retained
        rw [classes]
        refine ⟨projected,?_⟩
        simpa [gates_cons,stepGate,chosen,retained] using hCount

end
end CCO.AutomaticEPCore.IsoGateTower
