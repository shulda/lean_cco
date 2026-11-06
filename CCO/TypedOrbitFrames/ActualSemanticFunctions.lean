import CCO.TypedOrbitFrames.ActualKernelClauses

/-! Finitely many semantic term FUNCTIONS, not finitely many words.
Actual full kernels also control term-value infinitude over an arbitrary
full old equivalence fibre, even when that fibre is not a named sort. -/

namespace CCO.TypedOrbitFrames

open CCO.ParityHasse.Original CCO.TransitionClosure CCO.UnaryTermsReturn
open CCO.UnaryFreshFrames

universe u v w r
variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {G : Type r} [Group G] [∀ j : ι, MulAction G (X j)]

theorem original_actual_real_named_functions_finite
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    (nr2 : Selectors.OriginalNR2 S) (i : ι) :
    ((originalCompletedStructure S H sap nr2).NamedFunctions ⟨⟨i,.inl ()⟩⟩).Finite := by
  obtain ⟨x⟩ := S.nonemptySort i
  exact (originalCompletedStructure S H sap nr2).namedFunctions_finite
    (originalCompletedMotionSubgroup S H sap nr2)
    (original_completed_real_carrier_transitive S H sap nr2 i) ⟨.inl ⟨i,x⟩,rfl⟩
    (original_completed_all_singleton_closures_finite S H sap nr2 _)

def originalActualRealTermFunctions
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    (nr2 : Selectors.OriginalNR2 S) (i : ι) :
    Set (X i → OriginalCompletedNamedCarrier S H) :=
  {f | ∃ C, ∃ t : Term (originalCompletedLanguage S H sap nr2) ⟨⟨i,.inl ()⟩⟩ C,
    f = fun x => (originalCompletedStructure S H sap nr2).eval t (.inl ⟨i,x⟩)}

theorem original_actual_real_term_functions_finite
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    (nr2 : Selectors.OriginalNR2 S) (i : ι) :
    (originalActualRealTermFunctions S H sap nr2 i).Finite := by
  apply ((original_actual_real_named_functions_finite S H sap nr2 i).image
    (fun f x => f ⟨.inl ⟨i,x⟩,rfl⟩)).subset
  rintro f ⟨C,t,rfl⟩
  exact ⟨_,⟨C,t,rfl⟩,rfl⟩

theorem original_real_term_functions_equivariant
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    (nr2 : Selectors.OriginalNR2 S) {i : ι}
    (f : X i → OriginalCompletedNamedCarrier S H)
    (hf : f ∈ originalActualRealTermFunctions S H sap nr2 i) :
    letI := originalCompletedNamedAction S H
    Quotient.Equivariant (G := G) f := by
  letI := originalCompletedNamedAction S H
  obtain ⟨C,t,rfl⟩ := hf
  intro g x
  exact ((originalCompletedStructure S H sap nr2).aut_eval
    (originalCompletedMotionHom S H sap nr2 g) t (.inl ⟨i,x⟩)).symm

theorem original_full_kernel_fibre_values_infinite
    {i : ι} (hCover : OriginalAllFullCoversInfinite S (i := i))
    (E K : ColourEq S i) (hNot : ¬ E ≤ K) (a : X i)
    {V : Type*} (f : X i → V) (hK : ∀ x y, f x = f y ↔ K x y) :
    (Quotient.FibreValues (Quotient.mk E.val) f (Quotient.mk E.val a)).Infinite := by
  let g : Quotient K.val → V := Quotient.lift f (fun x y h => (hK x y).mpr h)
  have hInj : Function.Injective g := by
    intro x y h
    induction x using Quotient.inductionOn with
    | _ x =>
      induction y using Quotient.inductionOn with
      | _ y => exact Quotient.sound ((hK x y).mp h)
  let T := {q : Quotient K.val // q ∈ originalJClassesWithinHClass S E K a}
  letI : Infinite T := original_unforced_J_classes_in_H_fibre_infinite S hCover E K hNot a
  apply Set.infinite_of_injective_forall_mem
    (f := fun z : T => g z.val) (hInj.comp Subtype.val_injective)
  intro z
  obtain ⟨y,hy,hyq⟩ := z.property
  refine ⟨y,Quotient.sound (E.val.symm hy),?_⟩
  change g (Quotient.mk K.val y) = g z.val
  exact congrArg g hyq

end CCO.TypedOrbitFrames
