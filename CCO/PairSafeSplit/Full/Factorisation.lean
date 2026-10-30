import CCO.APCharacter.Totality

/-! B047 C14. Represented rigid products construct the intermediate reached
sort and both compatible actual arrows, without any SAP or STRONG premise. -/
set_option backward.isDefEq.respectTransparency.types false
universe u v w t
namespace CCO.PairSafeSplit.Full
open APCharacter RigidGroupoid.Geometry RigidGroupoid.Phase
noncomputable section
variable {ι : Type u} {X : ι → Type v} (S : AtomicSource.{u,v,w} ι X)
variable {G : Type t} [Group G] [∀ i, MulAction G (X i)]
variable (H : HomogeneousSource S G) (C : ExactCalculus S) {r : ι} {A : Kernel S r}

theorem rigid_product_factorisation (b c : Reached S A) {j : ι}
    (U : TRel X b.val j) (V : TRel X j c.val) (hU : FullExact S U) (hV : FullExact S V)
    (F : Arrow S (Reached.kernel H C b) (Reached.kernel H C c))
    (hUV : ∀ x z, TRel.comp U V x z → F.rel x z) :
    ∃ hj : Nonempty (Bridge S A j),
      ∃ F₁ : Arrow S (Reached.kernel H C b) (Reached.kernel H C ⟨j,hj⟩),
      ∃ F₂ : Arrow S (Reached.kernel H C ⟨j,hj⟩) (Reached.kernel H C c),
        (∀ x y, U x y → F₁.rel x y) ∧
        (∀ y z, V y z → F₂.rel y z) ∧ F₁.comp C F₂ = F := by
  obtain ⟨F₁,F₂,hU₁,hV₂,hprod,_⟩ := rigid_factorisation S H C hU hV F hUV
  let Troot := (Reached.rootArrow H C b).comp C (F₁.toArrow H C)
  have hj : Nonempty (Bridge S A j) := ⟨Troot.toBridge⟩
  have hB : F₁.targetKernel H C = Reached.kernel H C ⟨j,hj⟩ :=
    SourcePhase.reached_kernel_of_arrow Troot hj
  let R₁ : Arrow S (Reached.kernel H C b) (Reached.kernel H C ⟨j,hj⟩) :=
    hB ▸ F₁.toArrow H C
  let R₂ : Arrow S (Reached.kernel H C ⟨j,hj⟩) (Reached.kernel H C c) := hB ▸ F₂
  refine ⟨hj,R₁,R₂,?_,?_,?_⟩
  · intro x y hxy
    change (hB ▸ F₁.toArrow H C).rel x y
    rw [cast_target_rel]
    exact hU₁ x y hxy
  · intro x y hxy
    change (hB ▸ F₂).rel x y
    rw [cast_source_rel]
    exact hV₂ x y hxy
  · apply Arrow.ext
    change TRel.comp (hB ▸ F₁.toArrow H C).rel (hB ▸ F₂).rel = F.rel
    rw [cast_target_rel,cast_source_rel]
    exact hprod

end
end CCO.PairSafeSplit.Full
