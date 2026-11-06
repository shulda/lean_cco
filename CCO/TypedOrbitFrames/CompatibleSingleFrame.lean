import CCO.TypedOrbitFrames.CompatibleForcedValues

/-! The source CMF equation: ONE original real point generates a
compatible same-sort family and avoids all surplus closure values.
The actual real identity participates in the SAME simultaneous move. -/

namespace CCO.TypedOrbitFrames

open CCO.ParityHasse.Original CCO.TransitionClosure CCO.UnaryTermsReturn
open CCO.UnaryFreshFrames CCO.RealClosure.Bounds

universe u v w r
variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {G : Type r} [Group G] [∀ j : ι, MulAction G (X j)]

theorem original_typed_compatible_single_real_frame
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    (cco : SemanticCCO.{u,v,max u v,w} S)
    (nr2 : Selectors.OriginalNR2 S) {i : ι}
    (hCover : OriginalAllFullCoversInfinite S (i := i)) {m : Nat}
    (E : Fin m → OriginalNamedHiddenCoordinate S H i) (c : Fin m → X i)
    (hPair : ∀ j k, ∃ x : X i, (E j).val (c j) x ∧ (E k).val (c k) x)
    (B : Set (OriginalCompletedNamedCarrier S H)) (hB : B.Finite)
    (hAB : (originalCompletedStructure S H sap nr2).closure
      (originalCompatibleFamilyVertices S H E c) ⊆ B) :
    ∃ x : X i, x ∈ originalActualClassFibre S (fun j => (E j).val) c ∧
      (originalCompletedStructure S H sap nr2).closure
        (originalCompatibleFamilyVertices S H E c) ⊆
          (originalCompletedStructure S H sap nr2).closureAt (.inl ⟨i,x⟩) ∧
      (originalCompletedStructure S H sap nr2).closureAt (.inl ⟨i,x⟩) ∩ B =
        (originalCompletedStructure S H sap nr2).closure
          (originalCompatibleFamilyVertices S H E c) ∧
      (.inl ⟨i,x⟩ : OriginalCompletedNamedCarrier S H) ∉ B := by
  classical
  let K := originalActualMeetEquivalence S (fun j => (E j).val)
  letI : MulAction G (Quotient K.val) := originalColourEqQuotientAction S H K
  letI := originalCompletedNamedAction S H
  let p : X i → Quotient K.val := Quotient.mk K.val
  let T := originalActualRealTermFunctions S H sap nr2 i
  obtain ⟨x₀,hx₀⟩ := original_terminal_actual_pairwise_class_helly S H cco
    (sortNR2_of_originalNR2 S H nr2) (fun j => (E j).val) c hPair
  have hp : Quotient.Equivariant (G := G) p := by intro g x; rfl
  have hTerms : ∀ f ∈ T, Quotient.Equivariant (G := G) f := by
    intro f hf
    exact original_real_term_functions_equivariant S H sap nr2 f hf
  have hFinite : ((fun f : X i → OriginalCompletedNamedCarrier S H => f x₀) '' T).Finite :=
    (original_actual_real_term_functions_finite S H sap nr2 i).image _
  have hInfinite : ∀ f ∈ T, ¬ Quotient.KernelLe p f →
      (Quotient.FibreValues p f (p x₀)).Infinite := by
    rintro f ⟨C,t,rfl⟩ hUnforced
    obtain ⟨J,hJ⟩ := original_real_term_has_actual_full_kernel S H sap nr2 t
    have hNot : ¬ K ≤ J := by
      intro h
      apply hUnforced
      intro a b hab
      exact (hJ a b).mpr (h (Quotient.exact hab))
    exact original_full_kernel_fibre_values_infinite S hCover K J hNot x₀ _ hJ
  obtain ⟨x,hpx,hAvoid⟩ := Quotient.common_fibre_avoidance
    (G := G) (S.original_sort_transitive_of_homogeneous H i) p hp T hTerms
      x₀ hFinite hInfinite hB.toFinset
  have hx : x ∈ originalActualClassFibre S (fun j => (E j).val) c := by
    rw [original_actual_class_fibre_eq_full_meet_class S (fun j => (E j).val) c x₀ hx₀]
    exact K.val.symm (Quotient.exact hpx)
  have hGen := original_compatible_family_generated_by_common_real S H sap nr2 E c x hx
  refine ⟨x,hx,hGen,?_,?_⟩
  · apply Set.Subset.antisymm
    · rintro y ⟨hy,hyB⟩
      obtain ⟨f,⟨C,t,rfl⟩,hty⟩ :=
        ((originalCompletedStructure S H sap nr2).namedValues_eq_closureAt
          ⟨.inl ⟨i,x⟩,rfl⟩).symm ▸ hy
      change (originalCompletedStructure S H sap nr2).eval t (.inl ⟨i,x⟩) = y at hty
      have hForced : Quotient.KernelLe p
          (fun a => (originalCompletedStructure S H sap nr2).eval t (.inl ⟨i,a⟩)) := by
        by_contra hn
        apply hAvoid _ ⟨C,t,rfl⟩ hn
        exact hB.mem_toFinset.mpr (hty.symm ▸ hyB)
      exact hty ▸ original_compatible_forced_term_value_in_named_closure
        S H sap cco nr2 E c t hForced x hx
    · intro y hy
      exact ⟨hGen hy,hAB hy⟩
  · intro hxB
    let f : X i → OriginalCompletedNamedCarrier S H := fun a => .inl ⟨i,a⟩
    have hf : f ∈ T := ⟨_,.id _,rfl⟩
    have hUnforced : ¬ Quotient.KernelLe p f := by
      intro h
      apply original_nonidentity_finite_meet_ne_bot S H sap
        (fun j => (E j).val) (fun j => (E j).property.1)
      apply le_antisymm _ bot_le
      intro a b hab
      have heq := h a b (Quotient.sound hab)
      have hab' : a = b := by simpa only [f,Sum.inl.injEq,Sigma.mk.injEq,heq_eq_eq,true_and] using heq
      exact hab'
    exact hAvoid f hf hUnforced (hB.mem_toFinset.mpr hxB)

end CCO.TypedOrbitFrames
