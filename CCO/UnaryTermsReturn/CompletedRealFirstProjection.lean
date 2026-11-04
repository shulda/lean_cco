import CCO.UnaryTermsReturn.CompletedNamedReachability

universe u v w t
namespace CCO.UnaryTermsReturn
variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {G : Type t} [Group G] [∀ i : ι, MulAction G (X i)]

open CCO.TransitionClosure

theorem original_completed_real_path_first_projection
    (H : HomogeneousSource S G)
    (sap : AgeSAP S) (nr2 : Selectors.OriginalNR2 S)
    {i : ι} (x : X i) {v : OriginalCompletedNamedCarrier S H}
    (h : OriginalCompletedNamedReachable S H sap nr2
      (.inl (⟨i,x⟩ : Sigma X)) v) :
    v = .inl (⟨i,x⟩ : Sigma X) ∨
      ∃ D : OriginalNamedHiddenCoordinate S H i,
        OriginalCompletedNamedReachable S H sap nr2
          (originalCompletedNamedHiddenNode S H D
            (Quotient.mk D.val.val x)) v := by
  induction h with
  | refl => exact Or.inl rfl
  | step h e ih =>
      rcases ih with hroot | ⟨D,hpath⟩
      · rw [hroot] at e
        cases e with
        | projection J y =>
            exact Or.inr ⟨J,.refl _⟩
      · exact Or.inr ⟨D,.step hpath e⟩

end CCO.UnaryTermsReturn
