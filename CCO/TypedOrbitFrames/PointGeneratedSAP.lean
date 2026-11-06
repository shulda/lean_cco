import CCO.TypedOrbitFrames.CompletedInterpretation

/-! Source11 T03: old real homogeneity and the proved actual source
interpretation satisfy the accepted POINT-GENERATED SAP criterion.
The conclusion remains restricted to full point-generated objects and
full such common bases; no arbitrary hidden-orphan SAP is inferred. -/

namespace CCO.TypedOrbitFrames

open CCO.ParityHasse.Original CCO.TransitionClosure CCO.UnaryTermsReturn
open CCO.UnaryFreshFrames CCO.PointGeneratedSAP

universe u v w
variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable (H : HomogeneousSource S (TerminalPowers.FullAut S))

theorem original_completed_real_embedding_tagged_colour
    (sap : AgeSAP S) (nr2 : Selectors.OriginalNR2 S)
    (D : Set (originalCompletedOriginal S H sap nr2).Real)
    (f : (originalCompletedOriginal S H sap nr2).Embedding D) (p q : D) :
    taggedColour S ((originalCompletedRealEquiv S H sap nr2).symm (f.point p))
        ((originalCompletedRealEquiv S H sap nr2).symm (f.point q)) =
      taggedColour S ((originalCompletedRealEquiv S H sap nr2).symm p.val)
        ((originalCompletedRealEquiv S H sap nr2).symm q.val) := by
  let E := originalCompletedRealEquiv S H sap nr2
  obtain ⟨⟨i,x⟩,hp⟩ := original_completed_real_node_surjective S H sap nr2 p.val
  obtain ⟨⟨j,y⟩,hq⟩ := original_completed_real_node_surjective S H sap nr2 q.val
  obtain ⟨⟨i',x'⟩,hfp⟩ := original_completed_real_node_surjective S H sap nr2 (f.point p)
  obtain ⟨⟨j',y'⟩,hfq⟩ := original_completed_real_node_surjective S H sap nr2 (f.point q)
  have hi : i' = i := by
    have h := f.sort_eq p
    rw [← hfp,← hp] at h
    exact congrArg (fun C => C.down.1) h
  have hj : j' = j := by
    have h := f.sort_eq q
    rw [← hfq,← hq] at h
    exact congrArg (fun C => C.down.1) h
  subst i'
  subst j'
  have hpE : E ⟨i,x⟩ = p.val := hp
  have hqE : E ⟨j,y⟩ = q.val := hq
  have hfpE : E ⟨i,x'⟩ = f.point p := hfp
  have hfqE : E ⟨j,y'⟩ = f.point q := hfq
  change taggedColour S (E.symm (f.point p)) (E.symm (f.point q)) =
    taggedColour S (E.symm p.val) (E.symm q.val)
  rw [← hfpE,← hfqE,← hpE,← hqE]
  simp only [Equiv.symm_apply_apply]
  apply congrArg (fun c : Option (S.Atom i j) =>
    (⟨i,j,c⟩ : Σ i : ι, Σ j : ι, Option (S.Atom i j)))
  cases hxy : S.colour x y with
  | none =>
      apply (S.colour_none_iff x' y').mpr
      have hOld := (S.colour_none_iff x y).mp hxy
      have hpq : p = q := by
        apply Subtype.ext
        rw [← hp,← hq,hOld]
      apply original_completed_real_node_injective S H sap nr2
      exact hfp.trans ((congrArg f.point hpq).trans hfq.symm)
  | some a =>
      let name := originalCompletedOldAtomName S H a
      let xs : Fin ((originalCompletedLanguage S H sap nr2).arity name) → D := by
        change Fin 2 → D
        exact fun k => if k = 0 then p else q
      have hBase : (originalCompletedStructure S H sap nr2).rel name
          (fun k => (xs k).val.val) := by
        change originalCompletedCylinderBinaryPredicate S H name p.val.val q.val.val
        rw [← hp,← hq]
        exact (original_completed_old_atom_name_semantics S H a x y).mpr hxy
      have hMove := (f.rel_iff name ⟨⟨i,j,a⟩,rfl⟩ xs).mpr hBase
      change originalCompletedCylinderBinaryPredicate S H name (f.point p).val (f.point q).val at hMove
      rw [← hfp,← hfq] at hMove
      exact (original_completed_old_atom_name_semantics S H a x' y').mp hMove

/-- Genuine old real homogeneity, transferred to the EXACT real reduct
used by the point-generated criterion. Hidden homogeneity is not used. -/
theorem original_completed_original_homogeneous
    (sap : AgeSAP S) (nr2 : Selectors.OriginalNR2 S) :
    (originalCompletedOriginal S H sap nr2).Homogeneous := by
  intro D hD f g
  letI : Finite D := hD.to_subtype
  let E := originalCompletedRealEquiv S H sap nr2
  let ff : D → Sigma X := fun p => E.symm (f.point p)
  let gg : D → Sigma X := fun p => E.symm (g.point p)
  have hColours : ∀ p q, taggedColour S (ff p) (ff q) = taggedColour S (gg p) (gg q) := by
    intro p q
    exact (original_completed_real_embedding_tagged_colour S H sap nr2 D f p q).trans
      (original_completed_real_embedding_tagged_colour S H sap nr2 D g p q).symm
  obtain ⟨motion,hMotion⟩ := H.extends_finite_diagram ff gg hColours
  refine ⟨originalCompletedMotionOriginalAut S H sap nr2 motion,?_⟩
  intro p
  change E (motion • E.symm (f.point p)) = g.point p
  rw [hMotion p]
  exact E.apply_symm_apply (g.point p)

/-- `prop:typed-coordinate-sap`: a real source instance of the accepted
point-generated criterion. All structural, homogeneity and original
orbit obligations are proved; there is no hidden SAP provider premise. -/
theorem original_typed_point_generated_coordinate_sap
    (sap : AgeSAP S) (cco : SemanticCCO.{u,v,max u v,w} S)
    (nr2 : Selectors.OriginalNR2 S) :
    PointGeneratedSAP.AgeSAP (originalCompletedOriginal S H sap nr2) :=
  ((originalCompletedInterpretation S H sap nr2).typed_point_generated_sap_criterion
    (original_completed_original_homogeneous S H sap nr2)).mpr
      (original_completed_interpretation_PGO S H sap cco nr2)

/-- Source-facing form: full original Aut(M) and its homogeneity are
constructed from the actual old source; no extra full-group hypothesis
or equality with full hidden Aut is requested from the caller. -/
theorem original_source_typed_point_generated_coordinate_sap
    {G : Type*} [Group G] [∀ i : ι, MulAction G (X i)]
    (oldH : HomogeneousSource S G) (sap : AgeSAP S)
    (cco : SemanticCCO.{u,v,max u v,w} S) (nr2 : Selectors.OriginalNR2 S) :
    PointGeneratedSAP.AgeSAP
      (originalCompletedOriginal S (TerminalPowers.full_homogeneous S oldH) sap nr2) :=
  original_typed_point_generated_coordinate_sap S (TerminalPowers.full_homogeneous S oldH)
    sap cco nr2

end CCO.TypedOrbitFrames
