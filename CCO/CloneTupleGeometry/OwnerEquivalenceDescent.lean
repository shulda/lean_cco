import CCO.CloneTupleGeometry.OwnerTerminalGeometry

/-! Literal descent of FULL clone equivalences to the actual owner source.
This is a relation on the original owners, with invariance proved from
complete zero-clone colours; no quotient-action section or SAP is assumed. -/
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 250000
set_option maxHeartbeats 900000
universe u v w
namespace CCO.CloneTupleGeometry.OwnerStage
open APCharacter ParityHasse.Original TerminalPowers
noncomputable section
variable (B : OwnerStage.{u,v,w}) (i : B.Sorts)

def ownerEquivalence (U : ColourEq (CloneSAP.source B.source) i) : ColourEq B.source i :=
  ⟨Setoid.comap (fun x : B.Point i => (x,0)) U.val,by
    intro x y x' y' hc
    have ho : taggedColour B.source (⟨i,x⟩ : Sigma B.Point) ⟨i,y⟩ =
        taggedColour B.source (⟨i,x'⟩ : Sigma B.Point) ⟨i,y'⟩ :=
      congrArg (fun c => (⟨i,i,c⟩ : Age.Colour B.source)) hc
    have ht := zeroClonePoint_tagged B.source ho
    have hz : (CloneSAP.source B.source).colour (x,0) (y,0) =
        (CloneSAP.source B.source).colour (x',0) (y',0) := by
      exact eq_of_heq (Sigma.mk.inj (eq_of_heq (Sigma.mk.inj ht).2)).2
    exact U.property _ _ _ _ hz⟩

theorem clone_relation_iff_ownerEquivalence
    (U : ColourEq (CloneSAP.source B.source) i)
    (hK : fullCloneKernel B.source i ≤ U) (x y : CloneSAP.Carrier B.Point i) :
    U x y ↔ B.ownerEquivalence i U x.1 y.1 := by
  constructor
  · intro h
    exact U.val.trans (hK (show fullCloneKernel B.source i (x.1,0) x from rfl))
      (U.val.trans h (hK (show fullCloneKernel B.source i y (y.1,0) from rfl)))
  · intro h
    exact U.val.trans (hK (show fullCloneKernel B.source i x (x.1,0) from rfl))
      (U.val.trans h (hK (show fullCloneKernel B.source i (y.1,0) y from rfl)))

theorem ownerEquivalence_inf (U V : ColourEq (CloneSAP.source B.source) i) :
    B.ownerEquivalence i (U ⊓ V) = B.ownerEquivalence i U ⊓ B.ownerEquivalence i V := rfl

@[simp] theorem ownerEquivalence_cloneKernel :
    B.ownerEquivalence i (fullCloneKernel B.source i) = ⊥ := by
  apply ColourEq.ext
  intro x y
  rfl

theorem ownerEquivalence_ne_bot (U : ColourEq (CloneSAP.source B.source) i)
    (hK : fullCloneKernel B.source i ≤ U) (hne : U ≠ fullCloneKernel B.source i) :
    B.ownerEquivalence i U ≠ ⊥ := by
  intro he
  apply hne
  apply le_antisymm ?_ hK
  intro x y hxy
  have h := (B.clone_relation_iff_ownerEquivalence i U hK x y).mp hxy
  rw [he] at h
  exact h

/-- Transitivity makes every class of a genuine nonidentity owner
invariant equivalence nontrivial, at the SAME selected owner z. -/
theorem owner_equivalence_class_nontrivial (E : ColourEq B.source i)
    (hne : E ≠ ⊥) (z : B.Point i) : ∃ x : B.Point i, x ≠ z ∧ E x z := by
  have hex : ∃ p q : B.Point i, E p q ∧ p ≠ q := by
    by_contra hn
    apply hne
    apply ColourEq.ext
    intro p q
    constructor
    · intro hpq
      by_contra hne
      exact hn ⟨p,q,hpq,hne⟩
    · intro he
      change p = q at he
      subst q
      exact E.val.refl p
  obtain ⟨p,q,hpq,hne⟩ := hex
  obtain ⟨g,hg⟩ := B.source.original_sort_transitive_of_homogeneous B.homogeneous i q z
  refine ⟨g • p,?_,?_⟩
  · intro he
    exact hne (MulAction.injective g (he.trans hg.symm))
  · have he := (E.property (g • p) (g • q) p q (fullAut_colour B.source g i i p q)).mpr hpq
    simpa only [hg] using he

end
end CCO.CloneTupleGeometry.OwnerStage
