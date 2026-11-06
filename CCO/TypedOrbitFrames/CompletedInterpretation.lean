import CCO.TypedOrbitFrames.CompletedOriginalAutomorphisms
import CCO.PointGeneratedSAP.Source

/-! The actual source-specific PointGeneratedSAP.Interpretation. The
original real group is FULL Aut of the actual old relational reduct;
its lift is constructed from its proved old-colour permutation. -/

namespace CCO.TypedOrbitFrames

open CCO.ParityHasse.Original CCO.TransitionClosure CCO.UnaryTermsReturn
open CCO.UnaryFreshFrames CCO.PointGeneratedSAP

universe u v w
variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable (H : HomogeneousSource S (TerminalPowers.FullAut S))

theorem original_completed_real_value_image
    (sap : AgeSAP S) (nr2 : Selectors.OriginalNR2 S)
    (D : Set (originalCompletedOriginal S H sap nr2).Real) :
    Subtype.val '' D = Sum.inl '' ((originalCompletedRealEquiv S H sap nr2).symm '' D) := by
  ext x
  constructor
  · rintro ⟨p,hp,rfl⟩
    refine ⟨(originalCompletedRealEquiv S H sap nr2).symm p,⟨p,hp,rfl⟩,?_⟩
    exact congrArg Subtype.val ((originalCompletedRealEquiv S H sap nr2).apply_symm_apply p)
  · rintro ⟨_,⟨p,hp,rfl⟩,rfl⟩
    refine ⟨p,hp,?_⟩
    exact (congrArg Subtype.val
      ((originalCompletedRealEquiv S H sap nr2).apply_symm_apply p)).symm

/-- Actual canonical interpretation with ALL structural obligations
discharged. Full hidden homogeneity/SAP is neither an input nor a field. -/
noncomputable def originalCompletedInterpretation
    (sap : AgeSAP S) (nr2 : Selectors.OriginalNR2 S) :
    Interpretation (originalCompletedStructure S H sap nr2)
      (originalCompletedOriginal S H sap nr2) where
  lift := (originalCompletedMotionHom S H sap nr2).comp
    (originalCompletedOriginalFullAutHom S H sap nr2)
  lift_real g p := by
    obtain ⟨p,rfl⟩ := original_completed_real_node_surjective S H sap nr2 p
    rcases p with ⟨i,x⟩
    exact congrArg Subtype.val (original_completed_original_sort_perm_node S H sap nr2 g i x)
  locallyFinite D hD := by
    rw [original_completed_real_value_image]
    exact original_completed_structure_real_base_locally_finite S H sap nr2 _ (hD.image _)
  generating x := by
    obtain ⟨p,hp⟩ := original_completed_structure_point_generated S H sap nr2 x
    exact ⟨originalCompletedRealNode S H sap nr2 p,hp⟩

/-- The actual lifted full old-real automorphism group contains every
original full source motion, with precisely its already proved action. -/
theorem original_completed_interpretation_lift_motion
    (sap : AgeSAP S) (nr2 : Selectors.OriginalNR2 S) (g : TerminalPowers.FullAut S) :
    (originalCompletedInterpretation S H sap nr2).lift
        (originalCompletedMotionOriginalAut S H sap nr2 g) =
      originalCompletedMotionHom S H sap nr2 g := by
  change originalCompletedMotionHom S H sap nr2
    (originalCompletedOriginalFullAutHom S H sap nr2
      (originalCompletedMotionOriginalAut S H sap nr2 g)) = _
  rw [original_completed_full_aut_of_motion]

/-- All PGO orbit hypotheses of the accepted generic criterion are
actual source instances, via the proved original full real-base TOS. -/
theorem original_completed_interpretation_PGO
    (sap : AgeSAP S) (cco : SemanticCCO.{u,v,max u v,w} S)
    (nr2 : Selectors.OriginalNR2 S) :
    (originalCompletedInterpretation S H sap nr2).PGO := by
  classical
  intro D hD x hx
  let E := originalCompletedRealEquiv S H sap nr2
  let base : Set (Sigma X) := E.symm '' D
  have hBase : base.Finite := hD.image _
  have hClosure : (originalCompletedStructure S H sap nr2).closure (Subtype.val '' D) =
      originalCompletedRealBaseClosure S H sap nr2 base := by
    rw [original_completed_real_value_image,original_completed_structure_real_base_closure_eq]
  have hInf := original_completed_outside_real_base_orbit_infinite S H sap cco nr2 base
    hBase x (hClosure ▸ hx)
  apply Set.Infinite.mono ?_ hInf
  rintro y ⟨g,hg,hgx⟩
  apply ((originalCompletedInterpretation S H sap nr2).mem_orbitOver_iff D x y).mpr
  refine ⟨originalCompletedMotionOriginalAut S H sap nr2 g,?_,?_⟩
  · intro p hp
    obtain ⟨q,hq⟩ := original_completed_real_node_surjective S H sap nr2 p
    have hqBase : q ∈ base := by
      refine ⟨p,hp,?_⟩
      change E.symm p = q
      rw [← hq]
      exact E.symm_apply_apply q
    rw [← hq,original_completed_motion_original_aut_node,hg q hqBase]
  · rw [original_completed_interpretation_lift_motion]
    exact hgx

end CCO.TypedOrbitFrames
