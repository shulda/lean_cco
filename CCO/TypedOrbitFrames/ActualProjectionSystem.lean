import CCO.TypedOrbitFrames.RealTermNormalForms
import CCO.PairSafeSplit.Infinity.TypeFibres
import CCO.UnaryFreshFrames.Quotient.System

/-! Actual projection terms, their real/hidden sort carriers and the
original motion subgroup. No abstract quotient presentation is assumed. -/

namespace CCO.TypedOrbitFrames

open CCO.ParityHasse.Original CCO.TransitionClosure CCO.UnaryTermsReturn
open CCO.UnaryFreshFrames

universe u v w r
variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {G : Type r} [Group G] [∀ j : ι, MulAction G (X j)]

theorem original_completed_real_carrier_exists
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    (nr2 : Selectors.OriginalNR2 S) {i : ι}
    (y : (originalCompletedStructure S H sap nr2).Carrier ⟨⟨i,.inl ()⟩⟩) :
    ∃ x : X i, y.val = .inl ⟨i,x⟩ := by
  rcases y with ⟨y,hy⟩
  obtain ⟨C,q,hq⟩ := original_completed_coordinate_reading_exists S H y
  have hC : C = ⟨i,.inl ()⟩ :=
    (original_completed_reading_sort S H hq).symm.trans (congrArg ULift.down hy)
  cases hC
  cases hq with
  | real x => exact ⟨x,rfl⟩

theorem original_completed_hidden_carrier_exists
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    (nr2 : Selectors.OriginalNR2 S) {i : ι}
    (D : OriginalNamedHiddenCoordinate S H i)
    (y : (originalCompletedStructure S H sap nr2).Carrier ⟨⟨i,.inr D⟩⟩) :
    ∃ q : Quotient D.val.val, y.val = originalCompletedNamedHiddenNode S H D q := by
  rcases y with ⟨y,hy⟩
  obtain ⟨C,q,hq⟩ := original_completed_coordinate_reading_exists S H y
  have hC : C = ⟨i,.inr D⟩ :=
    (original_completed_reading_sort S H hq).symm.trans (congrArg ULift.down hy)
  cases hC
  cases hq with
  | hidden D q => exact ⟨q,rfl⟩

theorem original_completed_all_singleton_closures_finite
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    (nr2 : Selectors.OriginalNR2 S) (y : OriginalCompletedNamedCarrier S H) :
    ((originalCompletedStructure S H sap nr2).closureAt y).Finite := by
  obtain ⟨x,hx⟩ := original_completed_structure_point_generated S H sap nr2 y
  apply (show ((originalCompletedStructure S H sap nr2).closureAt (.inl x)).Finite from ?_).subset
    ((originalCompletedStructure S H sap nr2).closureAt_mono_of_mem hx)
  rw [original_completed_structure_closureAt_eq]
  exact original_completed_real_one_closure_finite S H sap nr2 x

noncomputable abbrev originalCompletedMotionSubgroup
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    (nr2 : Selectors.OriginalNR2 S) :
    Subgroup (originalCompletedStructure S H sap nr2).Aut :=
  (originalCompletedMotionHom S H sap nr2).range

theorem original_completed_real_carrier_transitive
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    (nr2 : Selectors.OriginalNR2 S) (i : ι) :
    letI := Structure.carrierAction (originalCompletedStructure S H sap nr2) ⟨⟨i,.inl ()⟩⟩
    Quotient.Transitive (G := originalCompletedMotionSubgroup S H sap nr2)
      (M := (originalCompletedStructure S H sap nr2).Carrier ⟨⟨i,.inl ()⟩⟩) := by
  letI := Structure.carrierAction (originalCompletedStructure S H sap nr2) ⟨⟨i,.inl ()⟩⟩
  intro x y
  obtain ⟨a,ha⟩ := original_completed_real_carrier_exists S H sap nr2 x
  obtain ⟨b,hb⟩ := original_completed_real_carrier_exists S H sap nr2 y
  obtain ⟨g,hg⟩ := S.original_sort_transitive_of_homogeneous H i a b
  refine ⟨⟨originalCompletedMotionHom S H sap nr2 g,⟨g,rfl⟩⟩,?_⟩
  apply Subtype.ext
  change originalCompletedNamedAct S H g x.val = y.val
  rw [ha,hb]
  exact congrArg (fun z : X i => (Sum.inl ⟨i,z⟩ : OriginalCompletedNamedCarrier S H)) hg

theorem original_projection_typedEval_surjective
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    (nr2 : Selectors.OriginalNR2 S) {i : ι}
    (D : OriginalNamedHiddenCoordinate S H i) :
    Function.Surjective ((originalCompletedStructure S H sap nr2).typedEval
      (originalProjectionAsTerm S H sap nr2 D)) := by
  intro y
  obtain ⟨q,hq⟩ := original_completed_hidden_carrier_exists S H sap nr2 D y
  induction q using Quotient.inductionOn with
  | _ a =>
      refine ⟨⟨.inl ⟨i,a⟩,rfl⟩,?_⟩
      apply Subtype.ext
      exact (original_projection_as_term_eval S H sap nr2 D a).trans hq.symm

theorem original_projection_typedEval_not_injective
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    (nr2 : Selectors.OriginalNR2 S) {i : ι}
    (D : OriginalNamedHiddenCoordinate S H i) :
    ¬ Function.Injective ((originalCompletedStructure S H sap nr2).typedEval
      (originalProjectionAsTerm S H sap nr2 D)) := by
  intro hInj
  obtain ⟨a⟩ := S.nonemptySort i
  obtain ⟨b,hab,hne⟩ := PairSafeSplit.Infinity.class_has_other S H D.val D.property.1 a
  have hEval : (originalCompletedStructure S H sap nr2).typedEval
        (originalProjectionAsTerm S H sap nr2 D) ⟨.inl ⟨i,a⟩,rfl⟩ =
      (originalCompletedStructure S H sap nr2).typedEval
        (originalProjectionAsTerm S H sap nr2 D) ⟨.inl ⟨i,b⟩,rfl⟩ := by
    apply Subtype.ext
    exact (original_projection_as_term_eval S H sap nr2 D a).trans
      ((congrArg (originalCompletedNamedHiddenNode S H D) (Quotient.sound hab)).trans
        (original_projection_as_term_eval S H sap nr2 D b).symm)
  have h := congrArg Subtype.val (hInj hEval)
  have hab' : a = b := by simpa only [Sum.inl.injEq,Sigma.mk.injEq,heq_eq_eq,true_and] using h
  exact hne hab'

end CCO.TypedOrbitFrames
