import CCO.UnfilteredEP.QuotientReturnTerms
import CCO.HiddenSAPReadings.SourceSupport

/-! C56: the WHOLE unary closure of two actual J-points has no
third point of that same named J sort. The statement ranges over all
named terms, including mixed upward/transition paths. -/

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

omit terminal in
/-- The faithful partial-function encoding has exactly the SAME closed
generated supports as the actual total-on-sort named interpretation. -/
theorem actual_partial_closure_eq (A : Set (OriginalCompletedNamedCarrier S H)) :
    (CCO.HiddenSAPReadings.originalPartialTarget S H sap nr2).closure A = (M).closure A := by
  let C := CCO.HiddenSAPReadings.originalPartialTarget S H sap nr2
  apply Set.Subset.antisymm
  · apply C.closure_minimal
      ((CCO.HiddenSAPReadings.partialTarget_closed_iff (M) _).mpr ((M).closure_closed A))
    exact (M).subset_closure A
  · apply (M).closure_minimal
      ((CCO.HiddenSAPReadings.partialTarget_closed_iff (M) _).mp (C.isClosed_closure A))
    exact C.subset_closure A

theorem quotient_singleton_closure_same_sort {i : ι}
    (D : CCO.TransitionClosure.OriginalNamedHiddenCoordinate S H i)
    (q : Quotient D.val.val) (y : OriginalCompletedNamedCarrier S H)
    (hy : (M).sort y = ⟨⟨i,.inr D⟩⟩)
    (hmem : y ∈ (M).closureAt (originalCompletedNamedHiddenNode S H D q)) :
    y = originalCompletedNamedHiddenNode S H D q := by
  obtain ⟨x,hx,s,term,hterm⟩ := hmem
  change x = originalCompletedNamedHiddenNode S H D q at hx
  subst x
  have hs : s = ⟨⟨i,.inr D⟩⟩ :=
    ((M).eval_sort term rfl).symm.trans ((congrArg (M).sort hterm).trans hy)
  subst s
  have hret := congrArg Subtype.val
    (actual_quotient_return_identity S H sap nr2 terminal D term
      ⟨originalCompletedNamedHiddenNode S H D q,rfl⟩)
  exact hterm.symm.trans hret

/-- Includes every proper term value, not merely displayed coordinate
positions or the two bare endpoints. -/
theorem quotient_pair_closure_same_sort {i : ι}
    (D : CCO.TransitionClosure.OriginalNamedHiddenCoordinate S H i)
    (q t : Quotient D.val.val) (y : OriginalCompletedNamedCarrier S H)
    (hy : (M).sort y = ⟨⟨i,.inr D⟩⟩)
    (hmem : y ∈ (M).closure
      {originalCompletedNamedHiddenNode S H D q,originalCompletedNamedHiddenNode S H D t}) :
    y = originalCompletedNamedHiddenNode S H D q ∨
      y = originalCompletedNamedHiddenNode S H D t := by
  obtain ⟨x,hx,hclosure⟩ := (M).mem_closure_iff_singleton.mp hmem
  rcases Set.mem_insert_iff.mp hx with hx | hx
  · subst x
    exact Or.inl (quotient_singleton_closure_same_sort S H sap nr2 terminal D q y hy hclosure)
  · have hx' : x = originalCompletedNamedHiddenNode S H D t := hx
    subst x
    exact Or.inr (quotient_singleton_closure_same_sort S H sap nr2 terminal D t y hy hclosure)

/-- C56's freshness conclusion for ANY third distinct actual J-value.
This is stronger than checking only a finite list of transition loops. -/
theorem quotient_third_point_outside_pair_closure {i : ι}
    (D : CCO.TransitionClosure.OriginalNamedHiddenCoordinate S H i)
    (q t z : Quotient D.val.val) (hzq : z ≠ q) (hzt : z ≠ t) :
    originalCompletedNamedHiddenNode S H D z ∉ (M).closure
      {originalCompletedNamedHiddenNode S H D q,originalCompletedNamedHiddenNode S H D t} := by
  intro hmem
  rcases quotient_pair_closure_same_sort S H sap nr2 terminal D q t _ rfl hmem with hq | ht
  · exact hzq (original_completed_hidden_node_injective S H D hq)
  · exact hzt (original_completed_hidden_node_injective S H D ht)

theorem quotient_third_point_outside_partial_pair_closure {i : ι}
    (D : CCO.TransitionClosure.OriginalNamedHiddenCoordinate S H i)
    (q t z : Quotient D.val.val) (hzq : z ≠ q) (hzt : z ≠ t) :
    originalCompletedNamedHiddenNode S H D z ∉
      (CCO.HiddenSAPReadings.originalPartialTarget S H sap nr2).closure
        {originalCompletedNamedHiddenNode S H D q,originalCompletedNamedHiddenNode S H D t} := by
  rw [actual_partial_closure_eq]
  exact quotient_third_point_outside_pair_closure S H sap nr2 terminal D q t z hzq hzt

end
end CCO.UnfilteredEP
