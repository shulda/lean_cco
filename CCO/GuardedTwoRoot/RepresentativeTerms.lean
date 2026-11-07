import CCO.HiddenSAPReadings.OrbitalNamedTerms

/-! Source14 C07--C08. Compose the actual named term with its root's
canonical real projection. Semantic functions, rather than syntax or
values at an unexplained test point, form a finite family: original
transitivity proves that one value determines the WHOLE function. -/

universe u v w r
namespace CCO.GuardedTwoRoot
open CCO.ParityHasse.Original CCO.TransitionClosure CCO.UnaryTermsReturn
open CCO.TypedOrbitFrames CCO.UnaryFreshFrames CCO.HiddenSAPReadings
noncomputable section
variable {ι : Type u} {X : ι → Type v} (S : AtomicSource.{u,v,w} ι X)
variable {G : Type r} [Group G] [∀ i, MulAction G (X i)]
variable (H : HomogeneousSource S G) (sap : AgeSAP S) (nr2 : Selectors.OriginalNR2 S)
local notation "Lang" => originalCompletedLanguage S H sap nr2
local notation "Hidden" => originalCompletedStructure S H sap nr2
local notation "Values" => OriginalCompletedNamedCarrier S H

/-- The root is either the literal real identity, or its actual named
F_J projection. No inverse quotient section is named by this term. -/
def rootBaseTerm (C : (Lang).Sorts) : Term Lang ⟨⟨C.down.1,.inl ()⟩⟩ C := by
  rcases C with ⟨⟨i,c⟩⟩
  cases c with
  | inl unit =>
    cases unit
    exact .id _
  | inr D =>
    exact Term.func (L := originalCompletedLanguage S H sap nr2)
      (⟨.inl ⟨i,D⟩⟩ : (Lang).Func) (.id _)

/-- Reading a named descendant from an original real representative. -/
def representativeTerm {C D : (Lang).Sorts} (t : Term Lang C D) :
    Term Lang ⟨⟨C.down.1,.inl ()⟩⟩ D := t.comp (rootBaseTerm S H sap nr2 C)

theorem representativeTerm_eval {C D : (Lang).Sorts} (t : Term Lang C D) (x : X C.down.1) :
    (Hidden).eval (representativeTerm S H sap nr2 t) (.inl ⟨C.down.1,x⟩) =
      (Hidden).eval t ((Hidden).eval (rootBaseTerm S H sap nr2 C) (.inl ⟨C.down.1,x⟩)) :=
  (Hidden).eval_comp t _ _

theorem rootBaseTerm_real {i : ι} (x : X i) :
    (Hidden).eval (rootBaseTerm S H sap nr2 ⟨⟨i,.inl ()⟩⟩) (.inl ⟨i,x⟩) =
      .inl ⟨i,x⟩ := rfl

theorem rootBaseTerm_proper {i : ι} (D : OriginalNamedHiddenCoordinate S H i) (x : X i) :
    (Hidden).eval (rootBaseTerm S H sap nr2 ⟨⟨i,.inr D⟩⟩) (.inl ⟨i,x⟩) =
      originalCompletedNamedHiddenNode S H D (Quotient.mk D.val.val x) := by
  change originalCompletedPrimitiveFunction S H sap nr2 (.inl ⟨i,D⟩) (.inl ⟨i,x⟩) = _
  exact original_completed_primitive_function_of_graph S H sap nr2
    (OriginalCompletedNamedLabelledStep.projection D x)

/-- A value equality at one input determines the two actual semantic
functions, even if their term syntax or stated output sorts differ. -/
theorem real_term_function_one_value {i : ι} {C D : (Lang).Sorts}
    (t : Term Lang ⟨⟨i,.inl ()⟩⟩ C) (s : Term Lang ⟨⟨i,.inl ()⟩⟩ D)
    (x : X i) (he : (Hidden).eval t (.inl ⟨i,x⟩) = (Hidden).eval s (.inl ⟨i,x⟩)) :
    (fun y : X i => (Hidden).eval t (.inl ⟨i,y⟩)) =
      (fun y : X i => (Hidden).eval s (.inl ⟨i,y⟩)) := by
  funext y
  obtain ⟨g,hg⟩ := S.original_sort_transitive_of_homogeneous H i x y
  have ht := (Hidden).aut_eval (originalCompletedMotionHom S H sap nr2 g) t (.inl ⟨i,x⟩)
  have hs := (Hidden).aut_eval (originalCompletedMotionHom S H sap nr2 g) s (.inl ⟨i,x⟩)
  change originalCompletedNamedAct S H g ((Hidden).eval t (.inl ⟨i,x⟩)) =
    (Hidden).eval t (.inl ⟨i,g • x⟩) at ht
  change originalCompletedNamedAct S H g ((Hidden).eval s (.inl ⟨i,x⟩)) =
    (Hidden).eval s (.inl ⟨i,g • x⟩) at hs
  rw [he] at ht
  exact hg ▸ (ht.symm.trans hs)

def RealTermFunctions (i : ι) : Set (X i → Values) :=
  {f | ∃ C : (Lang).Sorts, ∃ t : Term Lang ⟨⟨i,.inl ()⟩⟩ C,
    f = fun x => (Hidden).eval t (.inl ⟨i,x⟩)}

theorem real_term_functions_eval_injective {i : ι} (x : X i) :
    Set.InjOn (fun f : X i → Values => f x) (RealTermFunctions S H sap nr2 i) := by
  rintro f ⟨C,t,rfl⟩ g ⟨D,s,rfl⟩ he
  exact real_term_function_one_value S H sap nr2 t s x he

theorem real_term_functions_finite (i : ι) : (RealTermFunctions S H sap nr2 i).Finite := by
  obtain ⟨x⟩ := S.nonemptySort i
  apply Set.Finite.of_finite_image (f := fun f : X i → Values => f x) ?_
    (real_term_functions_eval_injective S H sap nr2 x)
  apply (original_completed_all_singleton_closures_finite S H sap nr2 (.inl ⟨i,x⟩)).subset
  rintro _ ⟨f,⟨C,t,rfl⟩,rfl⟩
  exact (Hidden).eval_mem_closed ((Hidden).closure_closed {Sum.inl ⟨i,x⟩}) t
    ((Hidden).subset_closure _ rfl)

/-- The finite family is bounded by the SAME source normal-code budget
as the completed singleton, after the explicit one-point injection. -/
theorem real_term_functions_card (i : ι) :
    Nat.card (RealTermFunctions S H sap nr2 i) ≤ originalSourceUniformNormalCodeBudget S H := by
  obtain ⟨x⟩ := S.nonemptySort i
  letI : Finite ((Hidden).closureAt (.inl ⟨i,x⟩)) :=
    (original_completed_all_singleton_closures_finite S H sap nr2 (.inl ⟨i,x⟩)).to_subtype
  let f : RealTermFunctions S H sap nr2 i → (Hidden).closureAt (.inl ⟨i,x⟩) := fun t =>
    ⟨t.val x,by
      obtain ⟨C,s,hs⟩ := t.property
      rw [hs]
      exact (Hidden).eval_mem_closed ((Hidden).closure_closed {Sum.inl ⟨i,x⟩}) s
        ((Hidden).subset_closure _ rfl)⟩
  have hf : Function.Injective f := by
    intro t s he
    exact Subtype.ext (real_term_functions_eval_injective S H sap nr2 x t.property s.property
      (congrArg Subtype.val he))
  exact (Nat.card_le_card_of_injective f hf).trans (by
    rw [original_completed_structure_closureAt_eq]
    exact original_completed_any_generator_uniform S H sap nr2 (.inl ⟨i,x⟩))

end
end CCO.GuardedTwoRoot
