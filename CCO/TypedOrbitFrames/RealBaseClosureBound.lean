import CCO.TypedOrbitFrames.RealBaseOrbitDichotomy
import CCO.UnaryTermsReturn.CompletedNamedFullClosureBound

/-! Source11 C21–C22: actual finite real-base closure and its uniform
linear bound. The union is over genuine real generators, not syntactic
unary words; empty real bases generate literally no vertices. -/

namespace CCO.TypedOrbitFrames

open CCO.UnaryTermsReturn CCO.TransitionClosure CCO.ParityHasse.Original

universe u v w r
variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {G : Type r} [Group G] [∀ j : ι, MulAction G (X j)]

theorem original_completed_real_one_closure_finite
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    (nr2 : Selectors.OriginalNR2 S) (x : Sigma X) :
    (originalCompletedNamedStepClosure S H sap nr2 (.inl x)).Finite := by
  rcases x with ⟨i,x⟩
  have hTarget : (originalRealOneGeneratedNamedValues S H sap nr2 x).Finite :=
    (Set.finite_singleton _).union
      ((original_real_named_term_values_finite S H sap nr2 x).image Sum.inr)
  have hImage :
      (originalCompletedCarrierForget S H ''
        originalCompletedNamedStepClosure S H sap nr2 (.inl ⟨i,x⟩)).Finite := by
    apply hTarget.subset
    rintro z ⟨y,hy,rfl⟩
    rcases original_completed_real_reachable_named_value S H sap nr2 x hy with
      hroot | ⟨d,hd⟩
    · rw [hroot]
      exact Or.inl rfl
    · rw [hd]
      exact Or.inr ⟨originalRealNamedTermChoiceValue S H sap nr2 x d,
        ⟨d,rfl⟩,rfl⟩
  exact hImage.of_finite_image (originalCompletedCarrierForget_injective S H).injOn

theorem original_completed_real_base_closure_insert
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    (nr2 : Selectors.OriginalNR2 S) (x : Sigma X) (D : Set (Sigma X)) :
    originalCompletedRealBaseClosure S H sap nr2 (insert x D) =
      originalCompletedNamedStepClosure S H sap nr2 (.inl x) ∪
        originalCompletedRealBaseClosure S H sap nr2 D := by
  ext y
  simp only [originalCompletedRealBaseClosure,Set.mem_iUnion,Set.mem_insert_iff,
    Set.mem_union]
  constructor
  · rintro ⟨p,hp,hpy⟩
    rcases hp with rfl | hp
    · exact Or.inl hpy
    · exact Or.inr ⟨p,hp,hpy⟩
  · rintro (h | ⟨p,hp,hpy⟩)
    · exact ⟨x,Or.inl rfl,h⟩
    · exact ⟨p,Or.inr hp,hpy⟩

/-- The FULL actual closure of a finite old base is finite, with no
assumption that the original or quotient universes themselves are finite. -/
theorem original_completed_real_base_closure_finite
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    (nr2 : Selectors.OriginalNR2 S) (D : Set (Sigma X)) (hD : D.Finite) :
    (originalCompletedRealBaseClosure S H sap nr2 D).Finite := by
  induction D,hD using Set.Finite.induction_on with
  | empty =>
      rw [original_completed_empty_real_base_closure]
      exact Set.finite_empty
  | @insert x D hx hD ih =>
      rw [original_completed_real_base_closure_insert]
      exact (original_completed_real_one_closure_finite S H sap nr2 x).union ih

/-- The source m_typ times |D| estimate counts distinct ACTUAL values.
There is no bound or finiteness claim on the syntax of transition words. -/
theorem original_completed_real_base_closure_uniform
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    (nr2 : Selectors.OriginalNR2 S) (D : Set (Sigma X)) (hD : D.Finite) :
    (originalCompletedRealBaseClosure S H sap nr2 D).ncard ≤
      originalSourceUniformNormalCodeBudget S H * D.ncard := by
  induction D,hD using Set.Finite.induction_on with
  | empty => simp [original_completed_empty_real_base_closure]
  | @insert x D hx hD ih =>
      rw [original_completed_real_base_closure_insert]
      calc
        _ ≤ (originalCompletedNamedStepClosure S H sap nr2 (.inl x)).ncard +
            (originalCompletedRealBaseClosure S H sap nr2 D).ncard :=
          Set.ncard_union_le _ _
        _ ≤ originalSourceUniformNormalCodeBudget S H +
            originalSourceUniformNormalCodeBudget S H * D.ncard :=
          Nat.add_le_add (original_completed_any_generator_uniform S H sap nr2 _) ih
        _ = originalSourceUniformNormalCodeBudget S H * (insert x D).ncard := by
          rw [Set.ncard_insert_of_notMem hx hD,Nat.mul_add,Nat.mul_one,Nat.add_comm]

/-- The displayed PG-ACL equation for the actual entire interpreted
carrier, under the original group and finite complete real bases only. -/
theorem original_completed_real_base_algebraic_closure_eq
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    (cco : SemanticCCO.{u,v,max u v,w} S)
    (nr2 : Selectors.OriginalNR2 S) (D : Set (Sigma X)) (hD : D.Finite) :
    {x | (originalCompletedRealBaseOrbit S H D x).Finite} =
      originalCompletedRealBaseClosure S H sap nr2 D := by
  ext x
  exact original_completed_real_base_finite_orbit_iff_closure S H sap cco nr2 D hD x

end CCO.TypedOrbitFrames
