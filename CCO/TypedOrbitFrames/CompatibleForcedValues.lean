import CCO.TypedOrbitFrames.ActualSemanticFunctions
import CCO.TypedOrbitFrames.InfiniteCommonClass
import CCO.TypedOrbitFrames.OrbitPrimeIntersection

/-! Compatible same-sort families: every forced real-source term value
is a LITERAL existing named term on ONE input coordinate vertex. -/

namespace CCO.TypedOrbitFrames

open CCO.ParityHasse.Original CCO.TransitionClosure CCO.UnaryTermsReturn
open CCO.UnaryFreshFrames CCO.RealClosure.Bounds

universe u v w r
variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {G : Type r} [Group G] [∀ j : ι, MulAction G (X j)]

def originalCompatibleFamilyVertices
    (H : HomogeneousSource S G) {i : ι} {m : Nat}
    (E : Fin m → OriginalNamedHiddenCoordinate S H i) (c : Fin m → X i) :
    Set (OriginalCompletedNamedCarrier S H) :=
  Set.range fun j => originalCompletedNamedHiddenNode S H (E j) (Quotient.mk (E j).val.val (c j))

theorem original_compatible_family_generated_by_common_real
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    (nr2 : Selectors.OriginalNR2 S) {i : ι} {m : Nat}
    (E : Fin m → OriginalNamedHiddenCoordinate S H i) (c : Fin m → X i)
    (x : X i) (hx : x ∈ originalActualClassFibre S (fun j => (E j).val) c) :
    (originalCompletedStructure S H sap nr2).closure (originalCompatibleFamilyVertices S H E c) ⊆
      (originalCompletedStructure S H sap nr2).closureAt (.inl ⟨i,x⟩) := by
  apply (originalCompletedStructure S H sap nr2).closure_minimal
    ((originalCompletedStructure S H sap nr2).closure_closed {.inl ⟨i,x⟩})
  rintro y ⟨j,rfl⟩
  have hEq := congrArg (originalCompletedNamedHiddenNode S H (E j)) (Quotient.sound (hx j))
  change originalCompletedNamedHiddenNode S H (E j) (Quotient.mk (E j).val.val (c j)) ∈ _
  rw [hEq]
  have hmem := (originalCompletedStructure S H sap nr2).typedEval_mem_closureAt
    (originalProjectionAsTerm S H sap nr2 (E j)) ⟨.inl ⟨i,x⟩,rfl⟩
  change (originalCompletedStructure S H sap nr2).eval
    (originalProjectionAsTerm S H sap nr2 (E j)) (.inl ⟨i,x⟩) ∈ _ at hmem
  rwa [original_projection_as_term_eval] at hmem

theorem original_compatible_forced_term_value_in_named_closure
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    (cco : SemanticCCO.{u,v,max u v,w} S)
    (nr2 : Selectors.OriginalNR2 S) {i : ι} {m : Nat}
    (E : Fin m → OriginalNamedHiddenCoordinate S H i) (c : Fin m → X i)
    {C : (originalCompletedLanguage S H sap nr2).Sorts}
    (t : Term (originalCompletedLanguage S H sap nr2) ⟨⟨i,.inl ()⟩⟩ C)
    (hForced : Quotient.KernelLe
      (Quotient.mk (originalActualMeetEquivalence S (fun j => (E j).val)).val)
      (fun x => (originalCompletedStructure S H sap nr2).eval t (.inl ⟨i,x⟩)))
    (x : X i) (hx : x ∈ originalActualClassFibre S (fun j => (E j).val) c) :
    (originalCompletedStructure S H sap nr2).eval t (.inl ⟨i,x⟩) ∈
      (originalCompletedStructure S H sap nr2).closure (originalCompatibleFamilyVertices S H E c) := by
  rcases original_real_term_literal_named_form S H sap nr2 t with
    ⟨_,hId⟩ | ⟨j,D,F,s,_,hVal⟩
  · have hBot : originalActualMeetEquivalence S (fun j => (E j).val) ≤ (⊥ : ColourEq S i) := by
      intro a b hab
      have heq := hForced a b (Quotient.sound hab)
      change (originalCompletedStructure S H sap nr2).eval t (.inl ⟨i,a⟩) =
        (originalCompletedStructure S H sap nr2).eval t (.inl ⟨i,b⟩) at heq
      rw [hId a,hId b] at heq
      have hab' : a = b := by simpa only [Sum.inl.injEq,Sigma.mk.injEq,heq_eq_eq,true_and] using heq
      exact hab'
    exact False.elim ((original_nonidentity_finite_meet_ne_bot S H sap
      (fun j => (E j).val) (fun j => (E j).property.1)) (le_antisymm hBot bot_le))
  · obtain ⟨K,_,theta,_,hPoint,hKernel⟩ := original_real_named_term_literal_QTNF S H sap nr2 D F s
    have hHK : originalActualMeetEquivalence S (fun j => (E j).val) ≤ K.val := by
      intro a b hab
      have heq := hForced a b (Quotient.sound hab)
      change (originalCompletedStructure S H sap nr2).eval t (.inl ⟨i,a⟩) =
        (originalCompletedStructure S H sap nr2).eval t (.inl ⟨i,b⟩) at heq
      rw [hVal a,hVal b] at heq
      exact (hKernel a b).mp ((original_completed_hidden_node_injective S H F) heq)
    letI : Lattice (ColourEq S i) := ColourEq.lattice S H
    have hMI : ExactCRT.FiniteOrder.BinaryMeetIrreducible K.val := by
      intro A B hAB
      exact (original_named_hidden_full_infIrred S H K).2 hAB
    obtain ⟨k,hEK⟩ := original_terminal_full_meet_prime_coordinate S H cco
      (sortNR2_of_originalNR2 S H nr2) K.val (original_named_hidden_full_proper S H K)
      hMI (fun j => (E j).val) hHK
    let factor := originalNamedForcedFactor S H sap nr2 (E k) K F hEK theta
    have hEq := (hPoint x).trans
      (originalNamedForcedFactor_real_point S H sap nr2 (E k) K F hEK theta x)
    have hClass : Quotient.mk (E k).val.val x = Quotient.mk (E k).val.val (c k) :=
      Quotient.sound ((E k).val.val.symm (hx k))
    change OriginalNamedRawUnaryTerm.eval S H sap nr2 s (Quotient.mk D.val.val x) =
      OriginalNamedRawUnaryTerm.eval S H sap nr2 factor (Quotient.mk (E k).val.val x) at hEq
    rw [hClass] at hEq
    rw [hVal,hEq,← original_named_word_as_term_eval S H sap nr2 factor]
    exact (originalCompletedStructure S H sap nr2).eval_mem_closed
      ((originalCompletedStructure S H sap nr2).closure_closed _) _
      ((originalCompletedStructure S H sap nr2).subset_closure _ ⟨k,rfl⟩)

end CCO.TypedOrbitFrames
