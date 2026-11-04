import CCO.UnaryTermsReturn.CompletedNamedFullClosureBound

universe u v w t
namespace CCO.UnaryTermsReturn
variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {G : Type t} [Group G] [∀ i : ι, MulAction G (X i)]
open CCO.TransitionClosure
open CCO.ParityHasse.Original

/-! B052 C13–C15: labelled graphs of genuine original named unary
primitives, retaining their actual original sorts and quotient kernels. -/
inductive OriginalCompletedNamedLabelledStep
    (H : HomogeneousSource S G)
    (sap : AgeSAP S) (nr2 : Selectors.OriginalNR2 S) :
    OriginalCompletedPrimitiveSymbol S H →
    OriginalCompletedNamedCarrier S H →
    OriginalCompletedNamedCarrier S H → Prop where
  | projection {i : ι}
      (D : OriginalNamedHiddenCoordinate S H i) (x : X i) :
      OriginalCompletedNamedLabelledStep H sap nr2
        (.inl ⟨i,D⟩)
        (.inl (⟨i,x⟩ : Sigma X))
        (originalCompletedNamedHiddenNode S H D
          (Quotient.mk D.val.val x))
  | upward {i : ι}
      (D E : OriginalNamedHiddenCoordinate S H i)
      (hDE : D.val ≤ E.val) (q : Quotient D.val.val) :
      OriginalCompletedNamedLabelledStep H sap nr2
        (.inr (.inl ⟨i,⟨(D,E),hDE⟩⟩))
        (originalCompletedNamedHiddenNode S H D q)
        (originalCompletedNamedHiddenNode S H E
          (Quot.mapRight hDE q))
  | raw {i j : ι}
      (a : OriginalNamedRawTransitionSymbol S H i j)
      (q : Quotient a.val.1.val.val) :
      OriginalCompletedNamedLabelledStep H sap nr2
        (.inr (.inr ⟨i,⟨j,a⟩⟩))
        (originalCompletedNamedHiddenNode S H a.val.1 q)
        (originalCompletedNamedHiddenNode S H
          (originalNamedRawTransitionSymbol_target S H sap nr2 a)
          (originalNamedRawTransitionSymbol_function S H sap nr2 a q))

theorem original_completed_labelled_step_forget
    (H : HomogeneousSource S G)
    (sap : AgeSAP S) (nr2 : Selectors.OriginalNR2 S)
    {s : OriginalCompletedPrimitiveSymbol S H}
    {x y : OriginalCompletedNamedCarrier S H}
    (h : OriginalCompletedNamedLabelledStep S H sap nr2 s x y) :
    OriginalCompletedNamedStep S H sap nr2 x y := by
  cases h with
  | projection D x => exact .projection D x
  | upward D E hDE q => exact .upward D E hDE q
  | raw a q => exact .rawTransition a q

theorem original_completed_step_has_actual_label
    (H : HomogeneousSource S G)
    (sap : AgeSAP S) (nr2 : Selectors.OriginalNR2 S)
    {x y : OriginalCompletedNamedCarrier S H}
    (h : OriginalCompletedNamedStep S H sap nr2 x y) :
    ∃ s : OriginalCompletedPrimitiveSymbol S H,
      OriginalCompletedNamedLabelledStep S H sap nr2 s x y := by
  cases h with
  | projection D x => exact ⟨.inl ⟨_,D⟩, .projection D x⟩
  | upward D E hDE q =>
      exact ⟨.inr (.inl ⟨_,⟨(D,E),hDE⟩⟩), .upward D E hDE q⟩
  | rawTransition a q =>
      exact ⟨.inr (.inr ⟨_,⟨_,a⟩⟩), .raw a q⟩

end CCO.UnaryTermsReturn
