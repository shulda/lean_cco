import CCO.TypedOrbitFrames.ActualProjectionSystem
import CCO.TypedOrbitFrames.InfiniteUnforcedClasses

/-! Kernels of ALL actual real-source terms are full original invariant
equivalences, with identity retained as bottom. The generic projection
kernel order is exactly the literal old order. -/

namespace CCO.TypedOrbitFrames

open CCO.ParityHasse.Original CCO.TransitionClosure CCO.UnaryTermsReturn
open CCO.UnaryFreshFrames

universe u v w r
variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {G : Type r} [Group G] [∀ j : ι, MulAction G (X j)]

theorem original_real_term_has_actual_full_kernel
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    (nr2 : Selectors.OriginalNR2 S) {i : ι}
    {C : (originalCompletedLanguage S H sap nr2).Sorts}
    (t : Term (originalCompletedLanguage S H sap nr2) ⟨⟨i,.inl ()⟩⟩ C) :
    ∃ K : ColourEq S i, ∀ x y : X i,
      ((originalCompletedStructure S H sap nr2).eval t (.inl ⟨i,x⟩) =
        (originalCompletedStructure S H sap nr2).eval t (.inl ⟨i,y⟩)) ↔ K x y := by
  rcases original_real_term_literal_named_form S H sap nr2 t with
    ⟨_,hId⟩ | ⟨j,D,E,s,_,hVal⟩
  · refine ⟨⊥,?_⟩
    intro x y
    simp only [hId,Sum.inl.injEq,Sigma.mk.injEq,heq_eq_eq,true_and,ColourEq.bot_apply]
  · obtain ⟨K,_,theta,_,_,hKernel⟩ := original_real_named_term_literal_QTNF S H sap nr2 D E s
    refine ⟨K.val,?_⟩
    intro x y
    rw [hVal x,hVal y]
    exact (original_completed_hidden_node_injective S H E).eq_iff.trans (hKernel x y)

theorem original_projection_kernelLe_iff_actual_order
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    (nr2 : Selectors.OriginalNR2 S) {i : ι}
    (J : OriginalNamedHiddenCoordinate S H i)
    {C : (originalCompletedLanguage S H sap nr2).Sorts}
    (t : Term (originalCompletedLanguage S H sap nr2) ⟨⟨i,.inl ()⟩⟩ C)
    (K : ColourEq S i)
    (hK : ∀ x y : X i,
      ((originalCompletedStructure S H sap nr2).eval t (.inl ⟨i,x⟩) =
        (originalCompletedStructure S H sap nr2).eval t (.inl ⟨i,y⟩)) ↔ K x y) :
    Quotient.KernelLe
        ((originalCompletedStructure S H sap nr2).typedEval
          (originalProjectionAsTerm S H sap nr2 J))
        ((originalCompletedStructure S H sap nr2).termFunction t) ↔ J.val ≤ K := by
  constructor
  · intro h x y hxy
    apply (hK x y).mp
    apply h ⟨.inl ⟨i,x⟩,rfl⟩ ⟨.inl ⟨i,y⟩,rfl⟩
    apply Subtype.ext
    exact (original_projection_as_term_eval S H sap nr2 J x).trans
      ((congrArg (originalCompletedNamedHiddenNode S H J) (Quotient.sound hxy)).trans
        (original_projection_as_term_eval S H sap nr2 J y).symm)
  · intro h x y hxy
    obtain ⟨a,ha⟩ := original_completed_real_carrier_exists S H sap nr2 x
    obtain ⟨b,hb⟩ := original_completed_real_carrier_exists S H sap nr2 y
    have hProj := congrArg Subtype.val hxy
    change (originalCompletedStructure S H sap nr2).eval
        (originalProjectionAsTerm S H sap nr2 J) x.val =
      (originalCompletedStructure S H sap nr2).eval
        (originalProjectionAsTerm S H sap nr2 J) y.val at hProj
    rw [ha,hb,original_projection_as_term_eval,original_projection_as_term_eval] at hProj
    have hJ := Quotient.exact ((original_completed_hidden_node_injective S H J) hProj)
    change (originalCompletedStructure S H sap nr2).eval t x.val =
      (originalCompletedStructure S H sap nr2).eval t y.val
    rw [ha,hb]
    exact (hK a b).mpr (h hJ)

/-- Infinite FULL relative indices yield cardinally infinite actual term
values in EVERY actual projection fibre, including identity outputs. -/
theorem original_real_term_infinite_fibre_of_actual_kernel
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    (nr2 : Selectors.OriginalNR2 S) {i : ι}
    (hCover : OriginalAllFullCoversInfinite S (i := i))
    (J : OriginalNamedHiddenCoordinate S H i)
    {C : (originalCompletedLanguage S H sap nr2).Sorts}
    (t : Term (originalCompletedLanguage S H sap nr2) ⟨⟨i,.inl ()⟩⟩ C)
    (K : ColourEq S i)
    (hK : ∀ x y : X i,
      ((originalCompletedStructure S H sap nr2).eval t (.inl ⟨i,x⟩) =
        (originalCompletedStructure S H sap nr2).eval t (.inl ⟨i,y⟩)) ↔ K x y)
    (hNot : ¬ J.val ≤ K)
    (b : (originalCompletedStructure S H sap nr2).Carrier ⟨⟨i,.inr J⟩⟩) :
    (Quotient.FibreValues
      ((originalCompletedStructure S H sap nr2).typedEval
        (originalProjectionAsTerm S H sap nr2 J))
      ((originalCompletedStructure S H sap nr2).termFunction t) b).Infinite := by
  classical
  obtain ⟨q,hq⟩ := original_completed_hidden_carrier_exists S H sap nr2 J b
  induction q using Quotient.inductionOn with
  | _ a =>
    let f : Quotient K.val → OriginalCompletedNamedCarrier S H :=
      Quotient.lift (fun y => (originalCompletedStructure S H sap nr2).eval t (.inl ⟨i,y⟩))
        (fun x y h => (hK x y).mpr h)
    have hInj : Function.Injective f := by
      intro x y h
      induction x using Quotient.inductionOn with
      | _ x =>
        induction y using Quotient.inductionOn with
        | _ y => exact Quotient.sound ((hK x y).mp h)
    let T := {q : Quotient K.val // q ∈ originalJClassesWithinHClass S J.val K a}
    letI : Infinite T := original_unforced_J_classes_in_H_fibre_infinite S hCover J.val K hNot a
    apply Set.infinite_of_injective_forall_mem
      (f := fun z : T => f z.val) (hInj.comp Subtype.val_injective)
    intro z
    obtain ⟨y,hy,hyq⟩ := z.property
    refine ⟨⟨.inl ⟨i,y⟩,rfl⟩,?_,?_⟩
    · apply Subtype.ext
      exact (original_projection_as_term_eval S H sap nr2 J y).trans
        ((congrArg (originalCompletedNamedHiddenNode S H J)
          (Quotient.sound (J.val.val.symm hy))).trans hq.symm)
    · change f (Quotient.mk K.val y) = f z.val
      exact congrArg f hyq

end CCO.TypedOrbitFrames
