import CCO.TypedOrbitFrames.CompletedOriginalReduct
import CCO.TypedOrbitFrames.OriginalSortPermutations

/-! Full automorphisms of the actual original real reduct preserve
exactly the original typed fine colours. No hidden automorphism is a
premise: these are permutations of the genuine real reduct only. -/

namespace CCO.TypedOrbitFrames

open CCO.ParityHasse.Original CCO.TransitionClosure CCO.UnaryTermsReturn
open CCO.UnaryFreshFrames CCO.PointGeneratedSAP

universe u v w r
variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {G : Type r} [Group G] [∀ j : ι, MulAction G (X j)]

noncomputable def originalCompletedOriginalSigmaPerm
    (H : HomogeneousSource S G) (sap : AgeSAP S) (nr2 : Selectors.OriginalNR2 S)
    (g : (originalCompletedOriginal S H sap nr2).Aut) : Equiv.Perm (Sigma X) :=
  (originalCompletedRealEquiv S H sap nr2).trans
    (g.val.trans (originalCompletedRealEquiv S H sap nr2).symm)

theorem original_completed_original_sigma_perm_node
    (H : HomogeneousSource S G) (sap : AgeSAP S) (nr2 : Selectors.OriginalNR2 S)
    (g : (originalCompletedOriginal S H sap nr2).Aut) (p : Sigma X) :
    originalCompletedRealNode S H sap nr2
        (originalCompletedOriginalSigmaPerm S H sap nr2 g p) =
      g • originalCompletedRealNode S H sap nr2 p :=
  (originalCompletedRealEquiv S H sap nr2).apply_symm_apply _

theorem original_completed_original_sigma_perm_sort
    (H : HomogeneousSource S G) (sap : AgeSAP S) (nr2 : Selectors.OriginalNR2 S)
    (g : (originalCompletedOriginal S H sap nr2).Aut) (p : Sigma X) :
    (originalCompletedOriginalSigmaPerm S H sap nr2 g p).1 = p.1 := by
  have h := (congrArg (fun z : (originalCompletedOriginal S H sap nr2).Real =>
      (originalCompletedStructure S H sap nr2).sort z.val)
    (original_completed_original_sigma_perm_node S H sap nr2 g p)).trans
      (g.property.1 (originalCompletedRealNode S H sap nr2 p))
  exact congrArg (fun C => C.down.1) h

noncomputable def originalCompletedOriginalSortPerm
    (H : HomogeneousSource S G) (sap : AgeSAP S) (nr2 : Selectors.OriginalNR2 S)
    (g : (originalCompletedOriginal S H sap nr2).Aut) (i : ι) : Equiv.Perm (X i) :=
  originalSigmaSortPermutation (originalCompletedOriginalSigmaPerm S H sap nr2 g)
    (original_completed_original_sigma_perm_sort S H sap nr2 g) i

theorem original_completed_original_sort_perm_node
    (H : HomogeneousSource S G) (sap : AgeSAP S) (nr2 : Selectors.OriginalNR2 S)
    (g : (originalCompletedOriginal S H sap nr2).Aut) (i : ι) (x : X i) :
    originalCompletedRealNode S H sap nr2
        ⟨i,originalCompletedOriginalSortPerm S H sap nr2 g i x⟩ =
      g • originalCompletedRealNode S H sap nr2 ⟨i,x⟩ :=
  (congrArg (originalCompletedRealNode S H sap nr2)
    (original_sigma_sort_permutation_tag _ _ i x)).trans
      (original_completed_original_sigma_perm_node S H sap nr2 g ⟨i,x⟩)

theorem original_completed_original_sort_perm_colour
    (H : HomogeneousSource S G) (sap : AgeSAP S) (nr2 : Selectors.OriginalNR2 S)
    (g : (originalCompletedOriginal S H sap nr2).Aut) (i j : ι) (x : X i) (y : X j) :
    S.colour (originalCompletedOriginalSortPerm S H sap nr2 g i x)
        (originalCompletedOriginalSortPerm S H sap nr2 g j y) = S.colour x y := by
  cases hxy : S.colour x y with
  | none =>
      apply (S.colour_none_iff _ _).mpr
      have hOld := (S.colour_none_iff x y).mp hxy
      apply original_completed_real_node_injective S H sap nr2
      rw [original_completed_original_sort_perm_node,
        original_completed_original_sort_perm_node,hOld]
  | some a =>
      let name := originalCompletedOldAtomName S H a
      let xs : Fin ((originalCompletedLanguage S H sap nr2).arity name) →
          (originalCompletedOriginal S H sap nr2).Real := by
        change Fin 2 → (originalCompletedOriginal S H sap nr2).Real
        exact fun k => if k = 0 then originalCompletedRealNode S H sap nr2 ⟨i,x⟩
          else originalCompletedRealNode S H sap nr2 ⟨j,y⟩
      have hBase : (originalCompletedStructure S H sap nr2).rel name
          (fun k => (xs k).val) := by
        change originalCompletedCylinderBinaryPredicate S H name
          (.inl ⟨i,x⟩) (.inl ⟨j,y⟩)
        exact (original_completed_old_atom_name_semantics S H a x y).mpr hxy
      have hMove := (g.property.2 name ⟨⟨i,j,a⟩,rfl⟩ xs).mpr hBase
      change originalCompletedCylinderBinaryPredicate S H name
        (g • originalCompletedRealNode S H sap nr2 ⟨i,x⟩).val
        (g • originalCompletedRealNode S H sap nr2 ⟨j,y⟩).val at hMove
      rw [← original_completed_original_sort_perm_node S H sap nr2 g i x,
        ← original_completed_original_sort_perm_node S H sap nr2 g j y] at hMove
      exact (original_completed_old_atom_name_semantics S H a _ _).mp hMove

noncomputable def originalCompletedOriginalFullAut
    (H : HomogeneousSource S G) (sap : AgeSAP S) (nr2 : Selectors.OriginalNR2 S)
    (g : (originalCompletedOriginal S H sap nr2).Aut) : TerminalPowers.FullAut S :=
  ⟨originalCompletedOriginalSortPerm S H sap nr2 g,
    original_completed_original_sort_perm_colour S H sap nr2 g⟩

noncomputable def originalCompletedOriginalFullAutHom
    (H : HomogeneousSource S G) (sap : AgeSAP S) (nr2 : Selectors.OriginalNR2 S) :
    (originalCompletedOriginal S H sap nr2).Aut →* TerminalPowers.FullAut S where
  toFun := originalCompletedOriginalFullAut S H sap nr2
  map_one' := by
    apply Subtype.ext
    funext i
    apply Equiv.ext
    intro x
    apply sigma_mk_injective
    apply original_completed_real_node_injective S H sap nr2
    change originalCompletedRealNode S H sap nr2
      ⟨i,originalCompletedOriginalSortPerm S H sap nr2 1 i x⟩ =
        originalCompletedRealNode S H sap nr2 ⟨i,x⟩
    rw [original_completed_original_sort_perm_node]
    exact one_smul _ _
  map_mul' g h := by
    apply Subtype.ext
    funext i
    apply Equiv.ext
    intro x
    apply sigma_mk_injective
    apply original_completed_real_node_injective S H sap nr2
    change originalCompletedRealNode S H sap nr2
      ⟨i,originalCompletedOriginalSortPerm S H sap nr2 (g * h) i x⟩ =
      originalCompletedRealNode S H sap nr2
        ⟨i,originalCompletedOriginalSortPerm S H sap nr2 g i
          (originalCompletedOriginalSortPerm S H sap nr2 h i x)⟩
    rw [original_completed_original_sort_perm_node,
      original_completed_original_sort_perm_node,
      original_completed_original_sort_perm_node]
    exact mul_smul g h _

noncomputable def originalCompletedMotionRealPerm
    (H : HomogeneousSource S G) (sap : AgeSAP S) (nr2 : Selectors.OriginalNR2 S)
    (g : G) : Equiv.Perm (originalCompletedOriginal S H sap nr2).Real :=
  (originalCompletedRealEquiv S H sap nr2).symm.trans
    ((MulAction.toPerm g).trans (originalCompletedRealEquiv S H sap nr2))

theorem original_completed_motion_real_perm_value
    (H : HomogeneousSource S G) (sap : AgeSAP S) (nr2 : Selectors.OriginalNR2 S)
    (g : G) (p : (originalCompletedOriginal S H sap nr2).Real) :
    (originalCompletedMotionRealPerm S H sap nr2 g p).val =
      originalCompletedNamedAct S H g p.val := by
  obtain ⟨p,rfl⟩ := original_completed_real_node_surjective S H sap nr2 p
  change (originalCompletedRealEquiv S H sap nr2
    (g • ((originalCompletedRealEquiv S H sap nr2).symm
      (originalCompletedRealEquiv S H sap nr2 p)))).val = _
  rw [Equiv.symm_apply_apply]
  rfl

/-- Every original source motion is an automorphism of this genuine
real reduct, as a restriction of its proved full-signature action. -/
noncomputable def originalCompletedMotionOriginalAut
    (H : HomogeneousSource S G) (sap : AgeSAP S) (nr2 : Selectors.OriginalNR2 S)
    (g : G) : (originalCompletedOriginal S H sap nr2).Aut :=
  ⟨originalCompletedMotionRealPerm S H sap nr2 g,by
    constructor
    · intro p
      rw [original_completed_motion_real_perm_value]
      exact congrArg ULift.up (original_completed_vertex_sort_invariant S H g p.val)
    · intro name _ xs
      have hValues : (fun k => (originalCompletedMotionRealPerm S H sap nr2 g (xs k)).val) =
          (fun k => originalCompletedNamedAct S H g (xs k).val) :=
        funext (fun k => original_completed_motion_real_perm_value S H sap nr2 g (xs k))
      rw [hValues]
      change (Fin 2 → (originalCompletedOriginal S H sap nr2).Real) at xs
      exact original_completed_binary_equivariant S H g name (xs 0).val (xs 1).val⟩

theorem original_completed_motion_original_aut_node
    (H : HomogeneousSource S G) (sap : AgeSAP S) (nr2 : Selectors.OriginalNR2 S)
    (g : G) (p : Sigma X) :
    originalCompletedMotionOriginalAut S H sap nr2 g • originalCompletedRealNode S H sap nr2 p =
      originalCompletedRealNode S H sap nr2 (g • p) := by
  apply Subtype.ext
  exact original_completed_motion_real_perm_value S H sap nr2 g _

theorem original_completed_full_aut_of_motion
    (H : HomogeneousSource S (TerminalPowers.FullAut S))
    (sap : AgeSAP S) (nr2 : Selectors.OriginalNR2 S) (g : TerminalPowers.FullAut S) :
    originalCompletedOriginalFullAutHom S H sap nr2
      (originalCompletedMotionOriginalAut S H sap nr2 g) = g := by
  apply Subtype.ext
  funext i
  apply Equiv.ext
  intro x
  apply sigma_mk_injective
  apply original_completed_real_node_injective S H sap nr2
  change originalCompletedRealNode S H sap nr2
    ⟨i,originalCompletedOriginalSortPerm S H sap nr2
      (originalCompletedMotionOriginalAut S H sap nr2 g) i x⟩ = _
  rw [original_completed_original_sort_perm_node,
    original_completed_motion_original_aut_node]
  rfl

theorem original_completed_motion_of_full_aut
    (H : HomogeneousSource S (TerminalPowers.FullAut S))
    (sap : AgeSAP S) (nr2 : Selectors.OriginalNR2 S)
    (g : (originalCompletedOriginal S H sap nr2).Aut) :
    originalCompletedMotionOriginalAut S H sap nr2
      (originalCompletedOriginalFullAutHom S H sap nr2 g) = g := by
  apply Subtype.ext
  apply Equiv.ext
  intro p
  obtain ⟨⟨i,x⟩,rfl⟩ := original_completed_real_node_surjective S H sap nr2 p
  change originalCompletedMotionOriginalAut S H sap nr2
      (originalCompletedOriginalFullAutHom S H sap nr2 g) •
        originalCompletedRealNode S H sap nr2 ⟨i,x⟩ = _
  rw [original_completed_motion_original_aut_node]
  exact original_completed_original_sort_perm_node S H sap nr2 g i x

end CCO.TypedOrbitFrames
