import CCO.UnaryTermsReturn.CompletedNamedHiddenBound
import CCO.UnaryTermsReturn.CompletedNamedRealBound
import CCO.UnaryTermsReturn.FullAdmissibleTransfer

universe u v w t
namespace CCO.UnaryTermsReturn
variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {G : Type t} [Group G] [∀ i : ι, MulAction G (X i)]

theorem original_completed_any_generator_uniform
    (H : HomogeneousSource S G)
    (sap : AgeSAP S) (nr2 : Selectors.OriginalNR2 S)
    (x : OriginalCompletedNamedCarrier S H) :
    (originalCompletedNamedStepClosure S H sap nr2 x).ncard ≤
      originalSourceUniformNormalCodeBudget S H := by
  cases x with
  | inl x =>
      rcases x with ⟨i,y⟩
      exact original_completed_real_primitive_closure_uniform
        S H sap nr2 y
  | inr x =>
      obtain ⟨i,D,q,hEq⟩ :=
        original_completed_hidden_value_has_named_witness S H x
      rw [hEq]
      exact original_completed_hidden_primitive_closure_uniform
        S H sap nr2 D q

theorem original_completed_finite_induced_generator_uniform
    (H : HomogeneousSource S G)
    (sap : AgeSAP S) (nr2 : Selectors.OriginalNR2 S)
    (C : Set (OriginalCompletedNamedCarrier S H))
    [Finite C]
    (hClosed : OriginalCompletedNamedStepClosed S H sap nr2 C)
    (x : C) :
    ({y : C | OriginalCompletedNamedRestrictedReachable
      S H sap nr2 C x y}).ncard ≤
        originalSourceUniformNormalCodeBudget S H := by
  have hFiniteRestricted :
      ({y : C | OriginalCompletedNamedRestrictedReachable
        S H sap nr2 C x y}).Finite :=
    Set.finite_univ.subset (Set.subset_univ _)
  have hImage :=
    original_completed_restricted_reachable_image
      S H sap nr2 C hClosed x
  have hFiniteAmbient :
      (originalCompletedNamedStepClosure S H sap nr2 x.val).Finite := by
    rw [← hImage]
    exact hFiniteRestricted.image Subtype.val
  exact original_completed_restricted_closure_uniform_from_ambient
    S H sap nr2 C hClosed x
    (originalSourceUniformNormalCodeBudget S H)
    hFiniteAmbient
    (original_completed_any_generator_uniform S H sap nr2 x.val)

end CCO.UnaryTermsReturn
