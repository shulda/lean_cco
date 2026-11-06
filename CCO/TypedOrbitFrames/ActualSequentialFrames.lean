import CCO.TypedOrbitFrames.ActualRequestEnumeration

/-! Source11 C42–C51, assembled for EVERY actual orphan vertex of A.
The final generator set is literally A_real union the selected real
representatives, with all forced factors and sequential avoidance. -/

namespace CCO.TypedOrbitFrames

open CCO.ParityHasse.Original CCO.TransitionClosure CCO.UnaryTermsReturn
open CCO.UnaryFreshFrames

universe u v w r
variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {G : Type r} [Group G] [∀ j : ι, MulAction G (X j)]

theorem original_typed_fresh_representatives
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    (nr2 : Selectors.OriginalNR2 S)
    (hCover : ∀ i : ι, OriginalAllFullCoversInfinite S (i := i))
    (A B F : Set (OriginalCompletedNamedCarrier S H))
    (hA : A.Finite) (hAcl : (originalCompletedStructure S H sap nr2).Closed A)
    (hB : B.Finite) (hF : F.Finite) (hAB : A ⊆ B) :
    ∃ n : Nat, ∃ r : Fin n → OriginalTypedQuotientRequest S H,
      ∃ f : Fin n → OriginalCompletedNamedCarrier S H,
      Function.Injective f ∧
      (∀ j, originalTypedRequestVertex S H (r j) ∈ A ∧
        (originalCompletedQuotientSystem S H sap nr2).IsChoice
          (originalTypedRequestAsSystemRequest S H sap nr2 (r j)) (f j) ∧
        (originalCompletedStructure S H sap nr2).sort (f j) ∈
          originalCompletedRealSorts S H sap nr2 ∧ f j ∉ B ∪ F) ∧
      (∀ b ∈ A, (originalCompletedStructure S H sap nr2).sort b ∉
        originalCompletedRealSorts S H sap nr2 →
        ∃ j, originalTypedRequestVertex S H (r j) = b) ∧
      (∀ j C (t : Term (originalCompletedLanguage S H sap nr2) ⟨⟨(r j).1,.inl ()⟩⟩ C),
        (Quotient.KernelLe
          ((originalCompletedStructure S H sap nr2).typedEval
            (originalProjectionAsTerm S H sap nr2 (r j).2.1))
          ((originalCompletedStructure S H sap nr2).termFunction t) →
          ∃ s : Term (originalCompletedLanguage S H sap nr2) ⟨⟨(r j).1,.inr (r j).2.1⟩⟩ C,
            (originalCompletedStructure S H sap nr2).eval t (f j) =
              (originalCompletedStructure S H sap nr2).eval s (originalTypedRequestVertex S H (r j)) ∧
            (originalCompletedStructure S H sap nr2).eval s (originalTypedRequestVertex S H (r j)) ∈ A) ∧
        (¬ Quotient.KernelLe
          ((originalCompletedStructure S H sap nr2).typedEval
            (originalProjectionAsTerm S H sap nr2 (r j).2.1))
          ((originalCompletedStructure S H sap nr2).termFunction t) →
          (originalCompletedStructure S H sap nr2).eval t (f j) ∉ B ∪ F ∧
          ∀ i, i < j → (originalCompletedStructure S H sap nr2).eval t (f j) ∉
            (originalCompletedStructure S H sap nr2).closureAt (f i))) ∧
      B ∩ (originalCompletedStructure S H sap nr2).closure
        ((A ∩ {x | (originalCompletedStructure S H sap nr2).sort x ∈
          originalCompletedRealSorts S H sap nr2}) ∪ Set.range f) = A := by
  classical
  let C := originalCompletedStructure S H sap nr2
  let Q := originalCompletedQuotientSystem S H sap nr2
  let motion := originalCompletedMotionSubgroup S H sap nr2
  obtain ⟨n,r,hrA,hrCover⟩ := original_finite_nonreal_request_enumeration S H sap nr2 A hA
  let requests := fun j => originalTypedRequestAsSystemRequest S H sap nr2 (r j)
  obtain ⟨f,hf,hP,hSep⟩ := Q.finite_sequential_choices motion
    (original_completed_quotient_system_source_transitive S H sap nr2)
    (original_completed_all_singleton_closures_finite S H sap nr2)
    (original_completed_quotient_system_kernel_clauses S H sap nr2 hCover)
    n requests (B ∪ F) (hB.union hF)
  have hBase (j : Fin n) : C.closureAt (originalTypedRequestVertex S H (r j)) ⊆ A :=
    C.closure_minimal hAcl (fun _ h => h ▸ hrA j)
  have hProjection (j : Fin n) :
      C.eval (originalProjectionAsTerm S H sap nr2 (r j).2.1) (f j) =
        originalTypedRequestVertex S H (r j) := congrArg Subtype.val (hP j).1.choose_spec
  have hRequestGen (j : Fin n) : originalTypedRequestVertex S H (r j) ∈ C.closureAt (f j) := by
    rw [← hProjection j]
    exact C.eval_mem_closed (C.closure_closed {f j}) _ (C.subset_closure {f j} rfl)
  let reals := A ∩ {x | C.sort x ∈ originalCompletedRealSorts S H sap nr2}
  let D := reals ∪ Set.range f
  have hGen : A ⊆ C.closure D := by
    intro b hb
    by_cases hReal : C.sort b ∈ originalCompletedRealSorts S H sap nr2
    · exact C.subset_closure D (Or.inl ⟨hb,hReal⟩)
    · obtain ⟨j,hj⟩ := hrCover b hb hReal
      rw [← hj]
      exact C.closure_mono (fun y hy => Or.inr ⟨j,hy.symm⟩) (hRequestGen j)
  refine ⟨n,r,f,hf,?_,hrCover,?_,?_⟩
  · intro j
    exact ⟨hrA j,(hP j).1,(hP j).2.1,(hP j).2.2.2⟩
  · intro j K t
    constructor
    · intro hForced
      obtain ⟨s,hs⟩ := original_projection_forced_named_factors S H sap nr2 (r j).2.1 K t hForced
      have hVal := hs ⟨f j,(hP j).1.choose⟩
      change C.eval t (f j) = C.eval s (C.eval
        (originalProjectionAsTerm S H sap nr2 (r j).2.1) (f j)) at hVal
      rw [hProjection] at hVal
      exact ⟨s,hVal,C.eval_mem_closed hAcl s (hrA j)⟩
    · intro hUnforced
      have hOff := Q.choice_unforced_not_in_base motion
        (original_completed_quotient_system_source_transitive S H sap nr2)
        (requests j) (f j) (hP j).1 K t hUnforced
      have hMem : C.eval t (f j) ∈ C.closureAt (f j) :=
        C.eval_mem_closed (C.closure_closed {f j}) t (C.subset_closure {f j} rfl)
      refine ⟨?_,?_⟩
      · intro hz
        have h := (hP j).2.2.1 ▸ (show C.eval t (f j) ∈ C.closureAt (f j) ∩ (B ∪ F) from ⟨hMem,hz⟩)
        exact hOff h.1
      · intro i hij hi
        exact hOff (hSep i j hij ⟨hMem,hi⟩)
  · apply Set.Subset.antisymm
    · rintro y ⟨hyB,hyD⟩
      obtain ⟨x,hx,hxy⟩ := C.mem_closure_iff_singleton.mp hyD
      rcases hx with hx | ⟨j,rfl⟩
      · exact (C.closure_minimal (A := {x}) hAcl (fun _ h => h ▸ hx.1)) hxy
      · have h := (hP j).2.2.1 ▸ (show y ∈ C.closureAt (f j) ∩ (B ∪ F) from ⟨hxy,Or.inl hyB⟩)
        exact hBase j h.1
    · intro y hy
      exact ⟨hAB hy,hGen hy⟩

end CCO.TypedOrbitFrames
