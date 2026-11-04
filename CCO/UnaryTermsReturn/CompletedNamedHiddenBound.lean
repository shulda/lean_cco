import CCO.UnaryTermsReturn.CompletedNamedReachabilityConverse

universe u v w t
namespace CCO.UnaryTermsReturn
variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {G : Type t} [Group G] [∀ i : ι, MulAction G (X i)]
open CCO.TransitionClosure
open CCO.ParityHasse.Original

theorem original_completed_hidden_primitive_closure_uniform
    (H : HomogeneousSource S G)
    (sap : AgeSAP S) (nr2 : Selectors.OriginalNR2 S)
    {i : ι} (D : OriginalNamedHiddenCoordinate S H i)
    (q : Quotient D.val.val) :
    (originalCompletedNamedStepClosure S H sap nr2
      (originalCompletedNamedHiddenNode S H D q)).ncard ≤
      originalSourceUniformNormalCodeBudget S H := by
  have hEq :
      originalCompletedNamedStepClosure S H sap nr2
        (originalCompletedNamedHiddenNode S H D q) =
      originalCompletedHiddenGeneratedValues S H sap nr2 D q := by
    apply Set.Subset.antisymm
    · intro y hy
      obtain ⟨j,E,w,heq⟩ :=
        original_completed_hidden_reachable_has_named_word
          S H sap nr2 D q hy
      rw [heq]
      refine ⟨originalCompletedHiddenTermHiddenValue S H sap nr2
        D q ⟨j,⟨E,w⟩⟩, ?_, rfl⟩
      exact ⟨⟨j,⟨E,w⟩⟩,rfl⟩
    · exact original_completed_hidden_values_reachable S H sap nr2 D q
  rw [hEq]
  exact original_completed_hidden_generated_values_uniform
    S H sap nr2 D q

end CCO.UnaryTermsReturn
