import CCO.APCharacter.SingleBridge
import CCO.RigidGroupoid.Phase.Factorisation

/-! Actual equality-inclusive fork totality. All intermediate bridge gates
are constructed and identified with the unique reached original gate. -/
set_option backward.isDefEq.respectTransparency.types false
universe u v w t
namespace CCO.APCharacter
open RigidGroupoid.Geometry RigidGroupoid.Phase
noncomputable section
variable {ι : Type u} {X : ι → Type v} {S : AtomicSource.{u,v,w} ι X}
variable {G : Type t} [Group G] [∀ i, MulAction G (X i)]
variable {H : HomogeneousSource S G} {C : ExactCalculus S} {r : ι} {A : Kernel S r}

theorem cast_target_rel {i j : ι} {K : Kernel S i} {B B' : Kernel S j}
    (e : B = B') (T : Arrow S K B) : (e ▸ T : Arrow S K B').rel = T.rel := by
  cases e
  rfl

theorem cast_source_rel {i j : ι} {B B' : Kernel S i} {K : Kernel S j}
    (e : B = B') (T : Arrow S B K) : (e ▸ T : Arrow S B' K).rel = T.rel := by
  cases e
  rfl

namespace SourcePhase
variable (P : SourcePhase S H C A)

theorem wrong_of_not_allows {i j : ι} (hi : Nonempty (Bridge S A i))
    (hj : Nonempty (Bridge S A j)) (ε η : Bit)
    (hv : P.validBit i ε) (hw : P.validBit j η)
    (D : TRel X i j)
    (h : ∀ x y, D x y → ¬P.allows (S.colour x y) ε η) :
    P.WrongSheet ⟨i,hi⟩ ⟨j,hj⟩ (η-ε) D := by
  letI := Reached.groupoid H C (A := A)
  intro x y hD
  have hn : ¬P.compatible ε η x y := by
    intro hh
    exact h x y hD ((P.allows_actual_iff x y ε η).mpr ⟨hv,hw,hh⟩)
  have ex : ∃ R : Arrow S (Reached.kernel H C ⟨i,hi⟩) (Reached.kernel H C ⟨j,hj⟩),
      R.rel x y ∧ ¬(η = ε + P.character.value R) := by
    by_contra hh
    apply hn
    intro hi' hj' R hR
    exact Classical.byContradiction fun he => hh ⟨R,hR,he⟩
  obtain ⟨R,hR,hχ⟩ := ex
  refine ⟨R,hR,?_⟩
  intro he
  apply hχ
  rw [he]
  abel

theorem wrong_saturate (b c : Reached S A) (δ : Bit) (D : TRel X b.val c.val)
    (h : P.WrongSheet b c δ D) :
    P.WrongSheet b c δ
      (TRel.comp (TRel.comp (Reached.kernel H C b).rel D) (Reached.kernel H C c).rel) := by
  rintro x y ⟨z,⟨a,hxa,haz⟩,hzy⟩
  obtain ⟨R,hR,hχ⟩ := h a z haz
  refine ⟨R,?_,hχ⟩
  rw [← R.right,← R.left]
  exact ⟨z,⟨a,hxa,hR⟩,hzy⟩

/-- The reached object is determined by the original root-to-sort bridge;
there is no supplied exact-descent or intermediate-kernel hypothesis. -/
theorem reached_kernel_of_arrow {j : ι} {B : Kernel S j} (T : Arrow S A B)
    (hj : Nonempty (Bridge S A j)) : B = Reached.kernel H C ⟨j,hj⟩ := by
  have ht : T.toBridge.targetKernel H C = B := by
    apply Kernel.ext_rel S
    exact T.target
  exact ht.symm.trans (bridge_targetKernel_unique S H C T.toBridge (Reached.bridge ⟨j,hj⟩))

theorem fork_totality (cco : SemanticCCO.{u,v,max u v,w} S)
    {i j k : ι} (a : Option (S.Atom i j)) (b : Option (S.Atom j k))
    (ε η θ : Bit) (hv : P.validBit i ε) (hw : P.validBit j η) (hz : P.validBit k θ)
    (ha : P.allows a ε η) (hb : P.allows b η θ)
    (hna : TRel.Nonempty (S.rawAtomRel a)) (hnb : TRel.Nonempty (S.rawAtomRel b)) :
    ∃ x z, TRel.comp (S.rawAtomRel a) (S.rawAtomRel b) x z ∧
      P.allows (S.colour x z) ε θ := by
  classical
  let R := S.rawAtomRel a
  let T := S.rawAtomRel b
  obtain ⟨xa,ya,haa⟩ := hna
  obtain ⟨xb,yb,hbb⟩ := hnb
  have hR : FullExact S R := by
    have h := fullExact_actual_atom S xa ya
    change S.colour xa ya = a at haa
    rwa [haa] at h
  have hT : FullExact S T := by
    have h := fullExact_actual_atom S xb yb
    change S.colour xb yb = b at hbb
    rwa [hbb] at h
  have hprod : FullExact S (TRel.comp R T) := C.comp hR hT
  by_contra hgoal
  have hbad : ∀ x z, TRel.comp R T x z → ¬P.allows (S.colour x z) ε θ := by
    intro x z hx ha
    exact hgoal ⟨x,z,hx,ha⟩
  have hi : Nonempty (Bridge S A i) := by
    by_contra hi
    obtain ⟨x,z,hxz⟩ := hprod.nonempty S
    apply hbad x z hxz
    exact (P.allows_actual_iff x z ε θ).mpr ⟨hv,hz,fun h _ _ _ => False.elim (hi h)⟩
  have hk : Nonempty (Bridge S A k) := by
    by_contra hk
    obtain ⟨x,z,hxz⟩ := hprod.nonempty S
    apply hbad x z hxz
    exact (P.allows_actual_iff x z ε θ).mpr ⟨hv,hz,fun _ h _ _ => False.elim (hk h)⟩
  let s : Reached S A := ⟨i,hi⟩
  let q : Reached S A := ⟨k,hk⟩
  let D := TRel.comp (TRel.comp (Reached.kernel H C s).rel (TRel.comp R T))
    (Reached.kernel H C q).rel
  have hD : FullExact S D := C.comp (C.comp (Reached.kernel H C s).exact hprod)
    (Reached.kernel H C q).exact
  have hL : TRel.comp (Reached.kernel H C s).rel D = D := by
    dsimp [D]
    rw [← TRel.comp_assoc,← TRel.comp_assoc,(Reached.kernel H C s).comp_self]
  have hRt : TRel.comp D (Reached.kernel H C q).rel = D := by
    dsimp [D]
    rw [TRel.comp_assoc,(Reached.kernel H C q).comp_self]
  obtain ⟨F,hF⟩ := P.wrong_exact_single_bridge cco s q (θ-ε) D hD hL hRt
    (P.wrong_saturate s q (θ-ε) (TRel.comp R T)
      (P.wrong_of_not_allows hi hk ε θ hv hz _ hbad))
  have hSub : ∀ x z, TRel.comp R T x z → F.rel x z := by
    intro x z hx
    rw [← hF]
    exact ⟨z,⟨x,(Reached.kernel H C s).setoid.refl x,hx⟩,
      (Reached.kernel H C q).setoid.refl z⟩
  obtain ⟨F₁,F₂,hRsub,hTsub,hComp,_⟩ := rigid_factorisation S H C hR hT F hSub
  let Troot := (Reached.rootArrow H C s).comp C (F₁.toArrow H C)
  have hj : Nonempty (Bridge S A j) := ⟨Troot.toBridge⟩
  have hB : F₁.targetKernel H C = Reached.kernel H C ⟨j,hj⟩ := reached_kernel_of_arrow Troot hj
  let F₁' : Arrow S (Reached.kernel H C s) (Reached.kernel H C ⟨j,hj⟩) :=
    hB ▸ F₁.toArrow H C
  let F₂' : Arrow S (Reached.kernel H C ⟨j,hj⟩) (Reached.kernel H C q) := hB ▸ F₂
  have hfirst : ∀ x y, R x y → F₁'.rel x y := by
    intro x y hxy
    change (hB ▸ F₁.toArrow H C).rel x y
    rw [cast_target_rel]
    exact hRsub x y hxy
  have hsecond : ∀ x y, T x y → F₂'.rel x y := by
    intro x y hxy
    change (hB ▸ F₂).rel x y
    rw [cast_source_rel]
    exact hTsub x y hxy
  letI := Reached.groupoid H C (A := A)
  have he₁ : η = ε + P.character.value F₁' := ha.2.2 xa ya haa hi hj F₁' (hfirst xa ya haa)
  have he₂ : θ = η + P.character.value F₂' := hb.2.2 xb yb hbb hj hk F₂' (hsecond xb yb hbb)
  have hf : F₁'.comp C F₂' = F := by
    apply Arrow.ext
    change TRel.comp (hB ▸ F₁.toArrow H C).rel (hB ▸ F₂).rel = F.rel
    rw [cast_target_rel,cast_source_rel]
    exact hComp
  have good : θ = ε + P.character.value F := by
    have hχ : P.character.value (F₁'.comp C F₂') =
        P.character.value F₁' + P.character.value F₂' := P.character.map_comp F₁' F₂'
    rw [← hf,hχ,he₂,he₁]
    abel
  obtain ⟨x,z,hxz⟩ := hprod.nonempty S
  have wrong := P.wrong_of_not_allows hi hk ε θ hv hz _ hbad x z hxz
  obtain ⟨F',hF',hχ⟩ := wrong
  have heq : F' = F := F'.eq_of_common_real_pair H F hF' (hSub x z hxz)
  apply hχ
  rw [heq]
  exact (eq_sub_iff_add_eq.mpr (by simpa only [add_comm] using good.symm))

end SourcePhase
end
end CCO.APCharacter
