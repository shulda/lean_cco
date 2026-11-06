import CCO.TypedOrbitFrames.CompletedStructureAction
import CCO.UnaryTermsReturn.LiteralRealFactorization
import CCO.UnaryFreshFrames.Quotient.Named

/-! Literal B049 quotient words are terms of the ACTUAL completed
structure. Their values agree on every existing quotient class. -/

namespace CCO.TypedOrbitFrames

open CCO.ParityHasse.Original CCO.TransitionClosure CCO.UnaryTermsReturn
open CCO.UnaryFreshFrames

universe u v w r
variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {G : Type r} [Group G] [∀ j : ι, MulAction G (X j)]

noncomputable def originalNamedWordAsTerm
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    (nr2 : Selectors.OriginalNR2 S)
    {i j : ι} {D : OriginalNamedHiddenCoordinate S H i}
    {E : OriginalNamedHiddenCoordinate S H j} :
    OriginalNamedRawUnaryTerm S H sap nr2 D E →
      Term (originalCompletedLanguage S H sap nr2)
        ⟨⟨i,.inr D⟩⟩ ⟨⟨j,.inr E⟩⟩
  | .ident D => .id _
  | .up t hEF => Term.func (L := originalCompletedLanguage S H sap nr2) (ULift.up (show OriginalCompletedPrimitiveSymbol S H from
      .inr (.inl ⟨_,⟨(_, _),hEF⟩⟩)))
      (originalNamedWordAsTerm H sap nr2 t)
  | .transition a t => Term.func (L := originalCompletedLanguage S H sap nr2) (ULift.up (show OriginalCompletedPrimitiveSymbol S H from
      .inr (.inr ⟨_,⟨_,a⟩⟩)))
      (originalNamedWordAsTerm H sap nr2 t)

theorem original_named_word_as_term_eval
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    (nr2 : Selectors.OriginalNR2 S)
    {i j : ι} {D : OriginalNamedHiddenCoordinate S H i}
    {E : OriginalNamedHiddenCoordinate S H j}
    (t : OriginalNamedRawUnaryTerm S H sap nr2 D E)
    (q : Quotient D.val.val) :
    (originalCompletedStructure S H sap nr2).eval
        (originalNamedWordAsTerm S H sap nr2 t)
        (originalCompletedNamedHiddenNode S H D q) =
      originalCompletedNamedHiddenNode S H E
        (OriginalNamedRawUnaryTerm.eval S H sap nr2 t q) := by
  induction t with
  | ident D => rfl
  | @up j D E F t hEF ih =>
      change originalCompletedPrimitiveFunction S H sap nr2
        (.inr (.inl ⟨j,⟨(E,F),hEF⟩⟩))
        ((originalCompletedStructure S H sap nr2).eval
          (originalNamedWordAsTerm S H sap nr2 t)
          (originalCompletedNamedHiddenNode S H D q)) = _
      rw [ih]
      exact original_completed_primitive_function_of_graph S H sap nr2
        (.upward _ _ hEF _)
  | @transition j k D a t ih =>
      change originalCompletedPrimitiveFunction S H sap nr2
        (.inr (.inr ⟨j,⟨k,a⟩⟩))
        ((originalCompletedStructure S H sap nr2).eval
          (originalNamedWordAsTerm S H sap nr2 t)
          (originalCompletedNamedHiddenNode S H D q)) = _
      rw [ih]
      exact original_completed_primitive_function_of_graph S H sap nr2 (.raw a _)

def originalProjectionAsTerm
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    (nr2 : Selectors.OriginalNR2 S)
    {i : ι} (D : OriginalNamedHiddenCoordinate S H i) :
    Term (originalCompletedLanguage S H sap nr2) ⟨⟨i,.inl ()⟩⟩ ⟨⟨i,.inr D⟩⟩ :=
  Term.func (L := originalCompletedLanguage S H sap nr2) (ULift.up (show OriginalCompletedPrimitiveSymbol S H from .inl ⟨i,D⟩)) (.id _)

theorem original_projection_as_term_eval
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    (nr2 : Selectors.OriginalNR2 S)
    {i : ι} (D : OriginalNamedHiddenCoordinate S H i) (x : X i) :
    (originalCompletedStructure S H sap nr2).eval
        (originalProjectionAsTerm S H sap nr2 D) (.inl ⟨i,x⟩) =
      originalCompletedNamedHiddenNode S H D (Quotient.mk D.val.val x) :=
  original_completed_primitive_function_of_graph S H sap nr2 (.projection D x)

end CCO.TypedOrbitFrames
