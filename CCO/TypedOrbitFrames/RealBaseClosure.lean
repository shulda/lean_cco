import CCO.UnaryTermsReturn.CompletedNamedStepClosure

/-!
# B053 D03/C05: full point-generated actual OLD real-base closure

The full transition-enriched terminal carrier consists of genuine old
reals and represented proper FULL MI quotient points. Its actual
unary closure over a real base is the UNION of the complete
one-generated B052 named-primitive closures, not the set of real
roots alone. This includes all upward and old RAW transition values
and allows an empty real base without an extra constant generator.

The named real-to-hidden projection F_J(x) is an actual primitive
edge from its old point x. Thus if that actual J-coordinate is
outside the FULL real-base unary closure, x cannot be in the old
base. This is source11 C05, retaining the literal represented
coordinate; it does NOT yet prove orbit infinitude.
-/

universe u v w t

namespace CCO.TypedOrbitFrames

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {G : Type t} [Group G] [∀ i : ι, MulAction G (X i)]

open CCO.UnaryTermsReturn
open CCO.TransitionClosure

/-- D03: FULL actual point-generated closure of an arbitrary
real-source base, including every genuine named quotient transition
and the old real identity. The empty real base has empty closure. -/
def originalCompletedRealBaseClosure
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    (nr2 : Selectors.OriginalNR2 S)
    (D : Set (Sigma X)) :
    Set (OriginalCompletedNamedCarrier S H) :=
  ⋃ p ∈ D, originalCompletedNamedStepClosure S H sap nr2 (.inl p)

/-- No nullary generator is introduced into source10: the actual
real-base closure of the EMPTY base is literally empty. -/
theorem original_completed_empty_real_base_closure
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    (nr2 : Selectors.OriginalNR2 S) :
    originalCompletedRealBaseClosure S H sap nr2 (∅ : Set (Sigma X)) =
      ∅ := by
  simp [originalCompletedRealBaseClosure]

/-- Every old actual named projection F_J(x) belongs to the
FULL one-generated closure of its actual old real point x. -/
theorem original_completed_real_projection_in_one_generated
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    (nr2 : Selectors.OriginalNR2 S)
    {i : ι} (J : OriginalNamedHiddenCoordinate S H i) (x : X i) :
    originalCompletedNamedHiddenNode S H J (Quotient.mk J.val.val x) ∈
      originalCompletedNamedStepClosure S H sap nr2
        (.inl (⟨i,x⟩ : Sigma X)) := by
  exact OriginalCompletedNamedReachable.step
    (.refl _) (.projection J x)

/-- C05: if a genuine represented proper J-class F_J(x) lies
outside the FULL actual quotient-transition closure of the finite
old base D, the REAL root x was not an old base vertex.
This implication uses NO unproved hidden SAP or CCO. -/
theorem original_unforced_projection_root_outside_real_base
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    (nr2 : Selectors.OriginalNR2 S)
    (D : Set (Sigma X))
    {i : ι} (J : OriginalNamedHiddenCoordinate S H i)
    (x : X i)
    (hunforced :
      originalCompletedNamedHiddenNode S H J (Quotient.mk J.val.val x)
        ∉ originalCompletedRealBaseClosure S H sap nr2 D) :
    (⟨i,x⟩ : Sigma X) ∉ D := by
  intro hx
  apply hunforced
  apply Set.mem_iUnion.mpr
  refine ⟨(⟨i,x⟩ : Sigma X), ?_⟩
  apply Set.mem_iUnion.mpr
  exact ⟨hx, original_completed_real_projection_in_one_generated
    S H sap nr2 J x⟩

end CCO.TypedOrbitFrames
