import CCO.TypedOrbitFrames.ActualNamedTerms

/-! Every actual well-sorted real-source term has the literal old
identity value or a B049 named projection/word value, uniformly on the
WHOLE original sort. Pointwise reachability is upgraded by the proved
original-group action and old sort transitivity. -/

namespace CCO.TypedOrbitFrames

open CCO.ParityHasse.Original CCO.TransitionClosure CCO.UnaryTermsReturn
open CCO.UnaryFreshFrames

universe u v w r
variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {G : Type r} [Group G] [∀ j : ι, MulAction G (X j)]

theorem original_real_terms_eq_of_one_value
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    (nr2 : Selectors.OriginalNR2 S) {i : ι}
    {C E : (originalCompletedLanguage S H sap nr2).Sorts}
    (t : Term (originalCompletedLanguage S H sap nr2) ⟨⟨i,.inl ()⟩⟩ C)
    (s : Term (originalCompletedLanguage S H sap nr2) ⟨⟨i,.inl ()⟩⟩ E)
    (x : X i)
    (hx : (originalCompletedStructure S H sap nr2).eval t (.inl ⟨i,x⟩) =
      (originalCompletedStructure S H sap nr2).eval s (.inl ⟨i,x⟩)) :
    ∀ y : X i, (originalCompletedStructure S H sap nr2).eval t (.inl ⟨i,y⟩) =
      (originalCompletedStructure S H sap nr2).eval s (.inl ⟨i,y⟩) := by
  intro y
  obtain ⟨g,hg⟩ := S.original_sort_transitive_of_homogeneous H i x y
  have ht := (originalCompletedStructure S H sap nr2).aut_eval
    (originalCompletedMotionHom S H sap nr2 g) t (.inl ⟨i,x⟩)
  have hs := (originalCompletedStructure S H sap nr2).aut_eval
    (originalCompletedMotionHom S H sap nr2 g) s (.inl ⟨i,x⟩)
  change originalCompletedNamedAct S H g _ =
    (originalCompletedStructure S H sap nr2).eval t (.inl ⟨i,g • x⟩) at ht
  change originalCompletedNamedAct S H g _ =
    (originalCompletedStructure S H sap nr2).eval s (.inl ⟨i,g • x⟩) at hs
  rw [hg] at ht hs
  exact ht.symm.trans ((congrArg (originalCompletedNamedAct S H g) hx).trans hs)

noncomputable def originalRealWordAsTerm
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    (nr2 : Selectors.OriginalNR2 S)
    {i j : ι} (D : OriginalNamedHiddenCoordinate S H i)
    (E : OriginalNamedHiddenCoordinate S H j)
    (t : OriginalNamedRawUnaryTerm S H sap nr2 D E) :
    Term (originalCompletedLanguage S H sap nr2) ⟨⟨i,.inl ()⟩⟩ ⟨⟨j,.inr E⟩⟩ :=
  (originalNamedWordAsTerm S H sap nr2 t).comp (originalProjectionAsTerm S H sap nr2 D)

theorem original_real_word_as_term_eval
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    (nr2 : Selectors.OriginalNR2 S)
    {i j : ι} (D : OriginalNamedHiddenCoordinate S H i)
    (E : OriginalNamedHiddenCoordinate S H j)
    (t : OriginalNamedRawUnaryTerm S H sap nr2 D E) (x : X i) :
    (originalCompletedStructure S H sap nr2).eval
        (originalRealWordAsTerm S H sap nr2 D E t) (.inl ⟨i,x⟩) =
      originalCompletedNamedHiddenNode S H E
        (OriginalNamedRawUnaryTerm.eval S H sap nr2 t (Quotient.mk D.val.val x)) := by
  exact ((originalCompletedStructure S H sap nr2).eval_comp
    (originalNamedWordAsTerm S H sap nr2 t)
    (originalProjectionAsTerm S H sap nr2 D) (.inl ⟨i,x⟩)).trans (by
      rw [original_projection_as_term_eval,original_named_word_as_term_eval])

/-- The actual identity output and actual represented MI output are
kept separate. The latter word and target are SAME for every real input. -/
theorem original_real_term_literal_named_form
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    (nr2 : Selectors.OriginalNR2 S) {i : ι}
    {C : (originalCompletedLanguage S H sap nr2).Sorts}
    (t : Term (originalCompletedLanguage S H sap nr2) ⟨⟨i,.inl ()⟩⟩ C) :
    (C = ⟨⟨i,.inl ()⟩⟩ ∧ ∀ x : X i,
      (originalCompletedStructure S H sap nr2).eval t (.inl ⟨i,x⟩) = .inl ⟨i,x⟩) ∨
    ∃ (j : ι) (D : OriginalNamedHiddenCoordinate S H i)
      (E : OriginalNamedHiddenCoordinate S H j)
      (s : OriginalNamedRawUnaryTerm S H sap nr2 D E),
      C = ⟨⟨j,.inr E⟩⟩ ∧ ∀ x : X i,
        (originalCompletedStructure S H sap nr2).eval t (.inl ⟨i,x⟩) =
          originalCompletedNamedHiddenNode S H E
            (OriginalNamedRawUnaryTerm.eval S H sap nr2 s (Quotient.mk D.val.val x)) := by
  obtain ⟨x⟩ := S.nonemptySort i
  have hmem := (originalCompletedStructure S H sap nr2).eval_mem_closed
    ((originalCompletedStructure S H sap nr2).closure_closed {.inl ⟨i,x⟩}) t
    ((originalCompletedStructure S H sap nr2).subset_closure {.inl ⟨i,x⟩} rfl)
  change _ ∈ (originalCompletedStructure S H sap nr2).closureAt (.inl ⟨i,x⟩) at hmem
  rw [original_completed_structure_closureAt_eq] at hmem
  rcases original_completed_real_reachable_named_value S H sap nr2 x hmem with
    hx | ⟨⟨j,⟨D,⟨E,s⟩⟩⟩,hx⟩
  · refine Or.inl ⟨?_,original_real_terms_eq_of_one_value S H sap nr2 t (.id _) x hx⟩
    have hs := (originalCompletedStructure S H sap nr2).eval_sort t (x := .inl ⟨i,x⟩) rfl
    rw [hx] at hs
    exact hs.symm
  · have hValue : (originalCompletedStructure S H sap nr2).eval t (.inl ⟨i,x⟩) =
        (originalCompletedStructure S H sap nr2).eval
          (originalRealWordAsTerm S H sap nr2 D E s) (.inl ⟨i,x⟩) := by
      rw [original_real_word_as_term_eval]
      exact hx
    refine Or.inr ⟨j,D,E,s,?_,?_⟩
    · have hs := (originalCompletedStructure S H sap nr2).eval_sort t (x := .inl ⟨i,x⟩) rfl
      rw [hx] at hs
      exact hs.symm
    · intro y
      exact (original_real_terms_eq_of_one_value S H sap nr2 t
        (originalRealWordAsTerm S H sap nr2 D E s) x hValue y).trans
        (original_real_word_as_term_eval S H sap nr2 D E s y)

end CCO.TypedOrbitFrames
