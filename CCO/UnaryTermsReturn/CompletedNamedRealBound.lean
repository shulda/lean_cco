import CCO.UnaryTermsReturn.CompletedRealFirstProjection
import CCO.UnaryTermsReturn.CompletedNamedReachabilityConverse
import CCO.UnaryTermsReturn.ActualGeneratedClosures

universe u v w t
namespace CCO.UnaryTermsReturn
variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {G : Type t} [Group G] [∀ i : ι, MulAction G (X i)]
open CCO.TransitionClosure
open CCO.ParityHasse.Original

theorem original_completed_real_reachable_named_value
    (H : HomogeneousSource S G)
    (sap : AgeSAP S) (nr2 : Selectors.OriginalNR2 S)
    {i : ι} (x : X i)
    {v : OriginalCompletedNamedCarrier S H}
    (h : OriginalCompletedNamedReachable S H sap nr2
      (.inl (⟨i,x⟩ : Sigma X)) v) :
    v = .inl (⟨i,x⟩ : Sigma X) ∨
      ∃ d : OriginalRealNamedTermChoice S H sap nr2 i,
        v = .inr (originalCompletedRealTermHiddenValue
          S H sap nr2 x d) := by
  rcases original_completed_real_path_first_projection
      S H sap nr2 x h with hroot | ⟨D,hpath⟩
  · exact Or.inl hroot
  · obtain ⟨j,E,w,heq⟩ :=
      original_completed_hidden_reachable_has_named_word
        S H sap nr2 D (Quotient.mk D.val.val x) hpath
    exact Or.inr ⟨⟨j,⟨D,⟨E,w⟩⟩⟩,heq⟩

theorem original_completed_real_primitive_closure_uniform
    (H : HomogeneousSource S G)
    (sap : AgeSAP S) (nr2 : Selectors.OriginalNR2 S)
    {i : ι} (x : X i) :
    (originalCompletedNamedStepClosure S H sap nr2
      (.inl (⟨i,x⟩ : Sigma X))).ncard ≤
      originalSourceUniformNormalCodeBudget S H := by
  have hEq : originalCompletedNamedStepClosure S H sap nr2
      (.inl (⟨i,x⟩ : Sigma X)) =
      originalCompletedRealGeneratedValues S H sap nr2 x := by
    apply Set.Subset.antisymm
    · intro v hv
      rcases original_completed_real_reachable_named_value
          S H sap nr2 x hv with hroot | ⟨d,hd⟩
      · rw [hroot]
        exact Or.inl rfl
      · rw [hd]
        exact Or.inr
          ⟨originalCompletedRealTermHiddenValue S H sap nr2 x d,
            ⟨d,rfl⟩,rfl⟩
    · exact original_completed_real_values_reachable S H sap nr2 x
  rw [hEq]
  exact original_completed_real_generated_values_uniform
    S H sap nr2 x

end CCO.UnaryTermsReturn
