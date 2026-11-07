import CCO.TerminalHiddenHN.GenericReadout
import CCO.TerminalHiddenHN.InterpretationNormalForms
import CCO.FullCode.Reconstruction
import CCO.FullCode.Consumer

/-! The marked presentation quotient is the literal original real-generated
closure. Its induced embedding recovers every partial function domain and
graph and every named non-order relation, retaining each old root mark. -/

universe u v w r l k
namespace CCO.TerminalHiddenHN.RealInterpretation
open CCO.UnaryFreshFrames
noncomputable section
variable {ι : Type u} {X : ι → Type v} {S : CCO.AtomicSource.{u,v,w} ι X}
variable {G : Type r} [Group G] [∀ i, MulAction G (X i)]
variable {U : Language.{max u l}} {V : Type k} {P : Structure U V}
variable (D : RealInterpretation (G := G) S U P) (H : CCO.HomogeneousSource S G)

abbrev readoutPresentationQuotient (A : CCO.FiniteInduced (X := X)) :=
  Quotient ((D.realObject A).presentationSetoid (D.normalForms H))

private def supportEquivRealClosure (A : CCO.FiniteInduced (X := X)) :
    (D.realObject A).support ≃ D.realClosure A where
  toFun x := ⟨x.val, by
    change x.val ∈ P.closure (D.realPoint '' A.vertices)
    rw [← D.realObject_support A]
    exact x.property⟩
  invFun x := ⟨x.val, by
    rw [D.realObject_support A]
    exact x.property⟩
  left_inv _ := Subtype.ext rfl
  right_inv _ := Subtype.ext rfl

/-- Defined normal-form presentations modulo their actual equality codes
recover the SAME generated support, including its original root marks. -/
def readoutQuotientEquiv (A : CCO.FiniteInduced (X := X)) :
    D.readoutPresentationQuotient H A ≃ D.realClosure A :=
  ((D.realObject A).presentationQuotientEquiv (D.normalForms H) (D.normalForms_valid H)).trans
    (D.supportEquivRealClosure A)

def readoutCoordinateClass {A : CCO.FiniteInduced (X := X)} (x : A.vertices) :
    D.readoutPresentationQuotient H A :=
  (D.realObject A).coordinateClass (D.normalForms H) (D.normalForms_valid H) x 0

theorem readoutQuotient_coordinate {A : CCO.FiniteInduced (X := X)} (x : A.vertices) :
    D.readoutQuotientEquiv H A (D.readoutCoordinateClass H x) = D.closurePoint x := by
  apply Subtype.ext
  change
    ((D.realObject A).presentationQuotientEquiv (D.normalForms H) (D.normalForms_valid H)
      ((D.realObject A).coordinateClass (D.normalForms H) (D.normalForms_valid H) x 0)).val =
        D.realPoint x.val
  exact congrArg (fun y : (D.realObject A).support => y.val)
    ((D.realObject A).quotient_coordinate (D.normalForms H) (D.normalForms_valid H) x 0)

abbrev readoutQuotientStructure (A : CCO.FiniteInduced (X := X)) :
    CCO.FullCode.Structure D.binaryLanguage (D.readoutPresentationQuotient H A) :=
  (D.realObject A).quotientStructure (D.normalForms H) (D.normalForms_valid H)

/-- This is the accepted full presentation-quotient embedding followed by
the actual induced inclusion, so it reflects full partial domains. -/
def readoutQuotientEmbedding (A : CCO.FiniteInduced (X := X)) :
    CCO.FullCode.Structure.Embedding (D.readoutQuotientStructure H A) D.binaryModel :=
  (D.codeModel.inclusion (D.realObject A).support
    (D.codeModel.isClosed_closure (D.realObject A).coordinates)).comp
      ((D.realObject A).quotientEmbedding (D.normalForms H) (D.normalForms_valid H))

theorem readoutQuotientEmbedding_point (A : CCO.FiniteInduced (X := X))
    (x : D.readoutPresentationQuotient H A) :
    (D.readoutQuotientEmbedding H A).point x = (D.readoutQuotientEquiv H A x).val := rfl

theorem readoutQuotientEmbedding_range (A : CCO.FiniteInduced (X := X)) :
    Set.range (D.readoutQuotientEmbedding H A).point = D.realClosure A := by
  ext x
  constructor
  · rintro ⟨q,rfl⟩
    exact (D.readoutQuotientEquiv H A q).property
  · intro hx
    obtain ⟨q,hq⟩ := (D.readoutQuotientEquiv H A).surjective ⟨x,hx⟩
    exact ⟨q,congrArg Subtype.val hq⟩

theorem readoutQuotient_sort (A : CCO.FiniteInduced (X := X))
    (x : D.readoutPresentationQuotient H A) :
    D.binaryModel.sort (D.readoutQuotientEquiv H A x).val =
      (D.readoutQuotientStructure H A).sort x :=
  (D.readoutQuotientEmbedding H A).sort_eq x

theorem readoutQuotient_function_iff (A : CCO.FiniteInduced (X := X))
    (F : D.binaryLanguage.Func) (x y : D.readoutPresentationQuotient H A) :
    y ∈ (D.readoutQuotientStructure H A).func F x ↔
      (D.readoutQuotientEquiv H A y).val ∈
        D.binaryModel.func F (D.readoutQuotientEquiv H A x).val := Iff.rfl

theorem readoutQuotient_domain_iff (A : CCO.FiniteInduced (X := X))
    (F : D.binaryLanguage.Func) (x : D.readoutPresentationQuotient H A) :
    (D.binaryModel.func F (D.readoutQuotientEquiv H A x).val).Nonempty ↔
      ((D.readoutQuotientStructure H A).func F x).Nonempty :=
  (D.readoutQuotientEmbedding H A).domain_iff F x

theorem readoutQuotient_unary_iff (A : CCO.FiniteInduced (X := X))
    (R : D.binaryLanguage.Unary) (x : D.readoutPresentationQuotient H A) :
    D.binaryModel.unary R (D.readoutQuotientEquiv H A x).val ↔
      (D.readoutQuotientStructure H A).unary R x :=
  (D.readoutQuotientEmbedding H A).unary_iff R x

theorem readoutQuotient_binary_iff (A : CCO.FiniteInduced (X := X))
    (R : D.binaryLanguage.Binary) (x y : D.readoutPresentationQuotient H A) :
    D.binaryModel.binary R (D.readoutQuotientEquiv H A x).val
      (D.readoutQuotientEquiv H A y).val ↔ (D.readoutQuotientStructure H A).binary R x y :=
  (D.readoutQuotientEmbedding H A).binary_iff R x y

end
end CCO.TerminalHiddenHN.RealInterpretation
