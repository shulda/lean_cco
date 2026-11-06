import CCO.TypedOrbitFrames.RealTermKernels

/-! Discharge BOTH kernel clauses of the actual named quotient system.
Forced factors are literal named words; unforced infinitude uses the
standing indices of the FULL original lattice, including real equality. -/

namespace CCO.TypedOrbitFrames

open CCO.ParityHasse.Original CCO.TransitionClosure CCO.UnaryTermsReturn
open CCO.UnaryFreshFrames

universe u v w r
variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {G : Type r} [Group G] [∀ j : ι, MulAction G (X j)]

theorem original_projection_forced_named_factors
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    (nr2 : Selectors.OriginalNR2 S) {i : ι}
    (J : OriginalNamedHiddenCoordinate S H i) :
    (originalCompletedStructure S H sap nr2).ForcedNamedFactors
      (originalProjectionAsTerm S H sap nr2 J) := by
  intro C t hForced
  rcases original_real_term_literal_named_form S H sap nr2 t with
    ⟨_,hId⟩ | ⟨j,D,E,s,hC,hVal⟩
  · have hBot : J.val ≤ (⊥ : ColourEq S i) :=
      (original_projection_kernelLe_iff_actual_order S H sap nr2 J t ⊥ (by
        intro x y
        simp only [hId,Sum.inl.injEq,Sigma.mk.injEq,heq_eq_eq,true_and,ColourEq.bot_apply])).mp hForced
    exact False.elim ((not_le_of_gt J.property.1) hBot)
  · cases hC
    obtain ⟨K,_,theta,hInj,hPoint,hKernel⟩ :=
      original_real_named_term_literal_QTNF S H sap nr2 D E s
    have hK : ∀ x y : X i,
        ((originalCompletedStructure S H sap nr2).eval t (.inl ⟨i,x⟩) =
          (originalCompletedStructure S H sap nr2).eval t (.inl ⟨i,y⟩)) ↔ K.val x y := by
      intro x y
      rw [hVal x,hVal y]
      exact (original_completed_hidden_node_injective S H E).eq_iff.trans (hKernel x y)
    have hJK := (original_projection_kernelLe_iff_actual_order S H sap nr2 J t K.val hK).mp hForced
    let factor := originalNamedForcedFactor S H sap nr2 J K E hJK theta
    refine ⟨originalNamedWordAsTerm S H sap nr2 factor,?_⟩
    intro x
    obtain ⟨a,ha⟩ := original_completed_real_carrier_exists S H sap nr2 x
    change (originalCompletedStructure S H sap nr2).eval t x.val = _
    rw [ha,hVal,original_projection_as_term_eval,original_named_word_as_term_eval]
    apply congrArg (originalCompletedNamedHiddenNode S H E)
    exact (hPoint a).trans (originalNamedForcedFactor_real_point S H sap nr2 J K E hJK theta a)

theorem original_projection_infinite_unforced_index
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    (nr2 : Selectors.OriginalNR2 S) {i : ι}
    (hCover : OriginalAllFullCoversInfinite S (i := i))
    (J : OriginalNamedHiddenCoordinate S H i) :
    (originalCompletedStructure S H sap nr2).InfiniteUnforcedIndex
      (originalProjectionAsTerm S H sap nr2 J) := by
  intro C t hUnforced b
  obtain ⟨K,hK⟩ := original_real_term_has_actual_full_kernel S H sap nr2 t
  have hNot : ¬ J.val ≤ K := by
    intro h
    exact hUnforced ((original_projection_kernelLe_iff_actual_order S H sap nr2 J t K hK).mpr h)
  exact original_real_term_infinite_fibre_of_actual_kernel S H sap nr2 hCover J t K hK hNot b

def originalCompletedRealSorts
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    (nr2 : Selectors.OriginalNR2 S) :
    Set (originalCompletedLanguage S H sap nr2).Sorts :=
  {C | ∃ i : ι, C.down = ⟨i,.inl ()⟩}

/-- Existing projection names present ALL actual represented hidden
sorts, including orphan vertices with no real root in the finite base. -/
noncomputable def originalCompletedQuotientSystem
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    (nr2 : Selectors.OriginalNR2 S) :
    (originalCompletedStructure S H sap nr2).NamedQuotientSystem
      (originalCompletedRealSorts S H sap nr2) where
  Index := ULift.{w} (Σ i : ι, OriginalNamedHiddenCoordinate S H i)
  projection q := {
    source := ⟨⟨q.down.1,.inl ()⟩⟩
    target := ⟨⟨q.down.1,.inr q.down.2⟩⟩
    term := originalProjectionAsTerm S H sap nr2 q.down.2
    surjective := original_projection_typedEval_surjective S H sap nr2 q.down.2
    strict := original_projection_typedEval_not_injective S H sap nr2 q.down.2 }
  source_real q := ⟨q.down.1,rfl⟩
  represents b hb := by
    cases b with
    | inl x => exact False.elim (hb ⟨x.1,rfl⟩)
    | inr b =>
      obtain ⟨i,J,q,hq⟩ := original_completed_hidden_value_has_named_witness S H b
      rw [hq]
      exact ⟨⟨⟨i,J⟩⟩,rfl⟩

theorem original_completed_quotient_system_kernel_clauses
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    (nr2 : Selectors.OriginalNR2 S)
    (hCover : ∀ i : ι, OriginalAllFullCoversInfinite S (i := i)) :
    (originalCompletedQuotientSystem S H sap nr2).KernelClauses := by
  intro q
  exact ⟨original_projection_forced_named_factors S H sap nr2 q.down.2,
    original_projection_infinite_unforced_index S H sap nr2 (hCover q.down.1) q.down.2⟩

theorem original_completed_quotient_system_source_transitive
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    (nr2 : Selectors.OriginalNR2 S) :
    (originalCompletedQuotientSystem S H sap nr2).SourceTransitive
      (originalCompletedMotionSubgroup S H sap nr2) := by
  intro q
  exact original_completed_real_carrier_transitive S H sap nr2 q.down.1

end CCO.TypedOrbitFrames
