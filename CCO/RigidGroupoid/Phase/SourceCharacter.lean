import CCO.RigidGroupoid.Phase.AbstractCharacter
import CCO.RigidGroupoid.Geometry.PointAction

/-! C31 instantiates the pure character construction on the ACTUAL reached
rigid groupoid. Its distinguished nonidentity arrow is explicit; no
dominance, parity pivot or preferred phase is assumed. -/

universe u v w t
namespace CCO.RigidGroupoid.Phase
open Geometry CategoryTheory

variable {ι : Type u} {X : ι → Type v} (S : AtomicSource.{u,v,w} ι X)
variable {G : Type t} [Group G] [∀ i, MulAction G (X i)]
variable (H : HomogeneousSource S G) (C : ExactCalculus S)

theorem actual_source_character {i : ι} (A : Kernel S i) (o : Reached S A)
    (t : Arrow S (Reached.kernel H C o) (Reached.kernel H C o))
    (ht : t ≠ Arrow.id (Reached.kernel H C o)) :
    letI := Reached.groupoid H C (A := A)
    ∃ χ : Abstract.Character (Reached S A), χ.value t = 1 ∧
      ∀ b (R : o ⟶ b),
        Abstract.transported t R ≠ 𝟙 b ∧
        χ.value (Abstract.transported t R) = 1 ∧
        ∀ T : o ⟶ b, Abstract.transported t R = Abstract.transported t T := by
  letI := Reached.groupoid H C (A := A)
  let K := Reached.kernel H C o
  letI := Isotropy.commGroup C K H
  letI := Isotropy.vectorSpace C K H
  letI := Isotropy.finiteType C K H
  let v : Additive (Isotropy S C K) := Additive.ofMul t
  have hv : v ≠ 0 := by
    intro he
    exact ht he
  obtain ⟨ℓ,hℓ⟩ := Abstract.detecting_character v hv
  let χ₀ : (o ⟶ o) → Abstract.Bit := fun R => ℓ (Additive.ofMul R)
  have hzero : χ₀ (𝟙 o) = 0 := ℓ.map_zero
  have hadd : ∀ R T : o ⟶ o, χ₀ (R ≫ T) = χ₀ R + χ₀ T := by
    intro R T
    exact ℓ.map_add (Additive.ofMul R) (Additive.ofMul T)
  let B : ∀ b : Reached S A, o ⟶ b := Reached.connectingArrow H C o
  have hB : B o = 𝟙 o := Arrow.inv_comp C (Reached.rootArrow H C o)
  let χ := Abstract.connectedCharacter o B χ₀ hzero hadd
  have hχ : χ.value t = 1 :=
    (Abstract.connectedCharacter_root o B χ₀ hzero hadd hB t).trans hℓ
  refine ⟨χ,hχ,?_⟩
  intro b R
  refine ⟨Abstract.transported_nonidentity t ht R,
    Abstract.transported_character χ t hχ R,?_⟩
  intro T
  apply Abstract.transported_independent t _ R T
  intro h
  exact Isotropy.comm C K H h t

end CCO.RigidGroupoid.Phase
