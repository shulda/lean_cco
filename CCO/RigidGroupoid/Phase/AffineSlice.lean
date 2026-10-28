import CCO.RigidGroupoid.Phase.AffineHelly
import CCO.RigidGroupoid.Phase.TranslatedHelly
import CCO.RigidGroupoid.Phase.CosetRelations

/-! C21: actual exact rigid slices are affine exact subgroup cosets.
The finite affine lemma's translate-Helly premise is supplied by actual
old exact relations, and exactness of the represented subgroup is proved
from the original slice's converse square. -/

universe u v w t
namespace CCO.RigidGroupoid.Phase
open Geometry

variable {ι : Type u} {X : ι → Type v} (S : AtomicSource.{u,v,w} ι X)
variable {G : Type t} [Group G] [∀ i, MulAction G (X i)]
variable (H : HomogeneousSource S G) (C : ExactCalculus S)
variable {i j : ι} {A : Kernel S i} {B : Kernel S j}

include H

theorem actual_support_affine (cco : SemanticCCO.{u,v,max u v,w} S)
    (d : Arrow S A B) {D : TRel X i j} (hD : FullExact S D)
    (hRight : TRel.comp D B.rel = D)
    (hCovered : ∀ x y, D x y → ∃ T : Arrow S A B, T.rel x y) :
    letI := Isotropy.commGroup C B H
    ∃ (z : Additive (Isotropy S C B)) (K : AddSubgroup (Additive (Isotropy S C B))),
      {h : Additive (Isotropy S C B) | h.toMul ∈ rigidSupport S C d D} =
        {h | h-z ∈ K} := by
  classical
  letI := Isotropy.commGroup C B H
  letI := Isotropy.finiteType C B H
  let E : Set (Additive (Isotropy S C B)) :=
    {h | h.toMul ∈ rigidSupport S C d D}
  have hE : E.Nonempty := by
    obtain ⟨h,hh⟩ := rigidSupport_nonempty S H C d hD hRight hCovered
    exact ⟨Additive.ofMul h,hh⟩
  have h2 : ∀ h : Additive (Isotropy S C B), h+h = 0 := by
    intro h
    exact Isotropy.square_one C B H h.toMul
  apply affine_coset_of_translate_helly h2 E hE
  intro F hPair
  let M := F.image Additive.toMul
  have hp : ∀ a ∈ M, ∀ b ∈ M, ∃ z : Isotropy S C B,
      z*a ∈ rigidSupport S C d D ∧ z*b ∈ rigidSupport S C d D := by
    intro a ha b hb
    obtain ⟨a',ha',rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨b',hb',rfl⟩ := Finset.mem_image.mp hb
    obtain ⟨z,hza,hzb⟩ := hPair a' ha' b' hb'
    exact ⟨z.toMul,hza,hzb⟩
  obtain ⟨z,hz⟩ := actual_support_translate_helly S H C cco d hD hRight hCovered M hp
  refine ⟨Additive.ofMul z,?_⟩
  intro a ha
  exact hz a.toMul (Finset.mem_image.mpr ⟨a,ha,rfl⟩)

theorem exact_rigid_coset (cco : SemanticCCO.{u,v,max u v,w} S)
    (d : Arrow S A B) {D : TRel X i j} (hD : FullExact S D)
    (_hLeft : TRel.comp A.rel D = D) (hRight : TRel.comp D B.rel = D)
    (hCovered : ∀ x y, D x y → ∃ T : Arrow S A B, T.rel x y) :
    ∃ (d' : Arrow S A B) (U : Subgroup (Isotropy S C B)),
      D = representedSlice S C d' (U : Set (Isotropy S C B)) ∧
      TRel.comp (TRel.converse D) D = isotropyUnion S C U ∧
      FullExact S (isotropyUnion S C U) := by
  classical
  letI := Isotropy.commGroup C B H
  obtain ⟨z,K,hK⟩ := actual_support_affine S H C cco d hD hRight hCovered
  let U : Subgroup (Isotropy S C B) := {
    carrier := {h | Additive.ofMul h ∈ K}
    one_mem' := K.zero_mem
    mul_mem' := fun ha hb => K.add_mem ha hb
    inv_mem' := fun ha => K.neg_mem ha
  }
  let d' := d.comp C z.toMul
  have hRep : D = representedSlice S C d' (U : Set (Isotropy S C B)) := by
    funext x y
    apply propext
    constructor
    · intro hxy
      rw [whole_rigid_support S H C d (hD.invariant S H) hRight hCovered] at hxy
      obtain ⟨h,hh,hxy⟩ := hxy
      have hm : Additive.ofMul h-z ∈ K := by
        have he : Additive.ofMul h ∈ {a : Additive (Isotropy S C B) |
            a.toMul ∈ rigidSupport S C d D} := hh
        rw [hK] at he
        exact he
      let s : Isotropy S C B := h*z.toMul⁻¹
      have hs : s ∈ U := hm
      have hzs : z.toMul*s = h := by dsimp [s]; simp [mul_comm]
      refine ⟨s,hs,?_⟩
      have he : d'.comp C s = d.comp C h :=
        (Arrow.comp_assoc C d z.toMul s).trans
          (congrArg (fun r : Arrow S B B => d.comp C r) hzs)
      exact Eq.mpr (congrArg (fun r : Arrow S A B => r.rel x y) he) hxy
    · rintro ⟨s,hs,hxy⟩
      let h : Isotropy S C B := z.toMul*s
      have hm : Additive.ofMul h-z = Additive.ofMul s := by
        change z + Additive.ofMul s-z = Additive.ofMul s
        abel
      have hh : h ∈ rigidSupport S C d D := by
        have he : Additive.ofMul h ∈ {a : Additive (Isotropy S C B) | a-z ∈ K} := by
          change Additive.ofMul h-z ∈ K
          rw [hm]
          exact hs
        rw [← hK] at he
        exact he
      rw [whole_rigid_support S H C d (hD.invariant S H) hRight hCovered]
      refine ⟨h,hh,?_⟩
      have he : d'.comp C s = d.comp C h := Arrow.comp_assoc C d z.toMul s
      exact Eq.mp (congrArg (fun r : Arrow S A B => r.rel x y) he) hxy
  have hSquare : TRel.comp (TRel.converse D) D = isotropyUnion S C U := by
    rw [hRep]
    exact representedSlice_square S H C d' U
  refine ⟨d',U,hRep,hSquare,?_⟩
  rw [← hSquare]
  exact C.comp (fullExact_converse S hD) hD

end CCO.RigidGroupoid.Phase
