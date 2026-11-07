import CCO.UnfilteredEP.ActualCoordinates
import CCO.UnfilteredEP.TerminalHolonomy
import CCO.TypedOrbitFrames.ActualProjectionSystem

/-! C34-C36: arbitrary ACTUAL unary terms starting at a represented
quotient, including terms mixing upward maps and transitions. Equality
after the onto real projection gives equality on the original quotient.
In particular every same-named-target return term is identity. -/

set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 250000
set_option maxHeartbeats 900000
universe u v w r
namespace CCO.UnfilteredEP
open CCO.UnaryTermsReturn CCO.UnaryFreshFrames CCO.TypedOrbitFrames
open CCO.ParityHasse.Original
noncomputable section
variable {ι : Type u} {X : ι → Type v} (S : AtomicSource.{u,v,w} ι X)
variable {G : Type r} [Group G] [∀ i, MulAction G (X i)]
variable (H : HomogeneousSource S G) (sap : AgeSAP S) (nr2 : Selectors.OriginalNR2 S)
variable (terminal : ∀ (i : ι) (E F : ColourEq S i), E < F →
  ∀ x : X i, Infinite (RelativeClass E.val F.val x))
include terminal
local notation "M" => originalCompletedStructure S H sap nr2
local notation "L" => originalCompletedLanguage S H sap nr2

/-- Quotient-start terms with the same target are literally equal as
typed maps. No unproved quotient homogeneity or chosen section occurs. -/
theorem actual_quotient_terms_eq {i : ι}
    (D : CCO.TransitionClosure.OriginalNamedHiddenCoordinate S H i)
    {s : (L).Sorts}
    (left right : Term L ⟨⟨i,.inr D⟩⟩ s) :
    (M).typedEval left = (M).typedEval right := by
  funext x
  let projection := originalProjectionAsTerm S H sap nr2 D
  obtain ⟨a,ha⟩ := actualRealTerm_surjective S H sap nr2 projection x
  have he := congrArg Subtype.val (congrFun
    (actual_real_terms_eq S H sap nr2 terminal
      (left.comp projection) (right.comp projection)) a)
  apply Subtype.ext
  change (M).eval left x.val = (M).eval right x.val
  have hproj : (M).eval projection (.inl ⟨i,a⟩) = x.val :=
    congrArg Subtype.val ha
  change (M).eval (left.comp projection) (.inl ⟨i,a⟩) =
    (M).eval (right.comp projection) (.inl ⟨i,a⟩) at he
  simpa only [Structure.eval_comp,hproj] using he

/-- C36 includes ALL quotient-to-same-quotient unary terms, not only
closed chains made solely from syntactic transition primitives. -/
theorem actual_quotient_return_identity {i : ι}
    (D : CCO.TransitionClosure.OriginalNamedHiddenCoordinate S H i)
    (term : Term L ⟨⟨i,.inr D⟩⟩ ⟨⟨i,.inr D⟩⟩)
    (x : (M).Carrier ⟨⟨i,.inr D⟩⟩) : (M).typedEval term x = x := by
  have h := congrFun (actual_quotient_terms_eq S H sap nr2 terminal D term (.id _)) x
  exact h

end
end CCO.UnfilteredEP
