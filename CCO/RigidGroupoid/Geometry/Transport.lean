import CCO.RigidGroupoid.Geometry.Interval
import CCO.RigidGroupoid.Geometry.PointAction

/-! Dominant involutions transport inside the actual exact-arrow groupoid.
Path independence uses only abelian SOURCE isotropy. Dominance is checked
against ORIGINAL exact equivalences via the original interval isomorphism. -/

universe u v w t
namespace CCO.RigidGroupoid.Geometry
variable {ι : Type u} {X : ι → Type v} {S : AtomicSource.{u,v,w} ι X}
variable (C : ExactCalculus S) {i j : ι} {A : Kernel S i} {B : Kernel S j}

namespace Arrow
theorem inverse_composite (R : Arrow S A B) {k : ι} {D : Kernel S k} (T : Arrow S B D) :
    (R.comp C T).inv = T.inv.comp C R.inv := ext (TRel.converse_comp R.rel T.rel)
end Arrow

def transport (t : Arrow S A A) (R : Arrow S A B) : Arrow S B B :=
  R.inv.comp C (t.comp C R)

@[simp] theorem transport_id (R : Arrow S A B) : transport C (Arrow.id A) R = Arrow.id B := by
  simp only [transport,Arrow.id_comp,Arrow.inv_comp]

theorem transport_inv_transport (R : Arrow S A B) (t : Arrow S A A) :
    transport C (transport C t R) R.inv = t := by
  simp only [transport,Arrow.inv_inv,Arrow.comp_assoc,Arrow.comp_inv,Arrow.comp_id]
  rw [← Arrow.comp_assoc,Arrow.comp_inv,Arrow.id_comp]

def isotropyEquiv (R : Arrow S A B) : Arrow S A A ≃ Arrow S B B where
  toFun t := transport C t R
  invFun u := transport C u R.inv
  left_inv := transport_inv_transport C R
  right_inv u := by
    have h := transport_inv_transport C R.inv u
    simpa only [Arrow.inv_inv] using h

theorem transport_nonidentity {t : Arrow S A A} (ht : t ≠ Arrow.id A) (R : Arrow S A B) :
    transport C t R ≠ Arrow.id B := by
  intro h
  apply ht
  apply (isotropyEquiv C R).injective
  exact h.trans (transport_id C R).symm

variable {G : Type t} [Group G] [∀ i, MulAction G (X i)]
variable (H : HomogeneousSource S G)
include H

theorem transport_path_independent (t : Arrow S A A) (R T : Arrow S A B) :
    transport C t R = transport C t T := by
  let h := T.comp C R.inv
  have hf : h.comp C R = T := by
    dsimp only [h]
    rw [Arrow.comp_assoc,Arrow.inv_comp,Arrow.comp_id]
  have hc : h.inv.comp C t = t.comp C h.inv := Isotropy.comm C A H h.inv t
  have hinner : (h.inv.comp C t).comp C h = t := by
    rw [hc,Arrow.comp_assoc,Arrow.inv_comp,Arrow.comp_id]
  symm
  calc
    transport C t T = transport C t (h.comp C R) := congrArg (transport C t) hf.symm
    _ = R.inv.comp C (((h.inv.comp C t).comp C h).comp C R) := by
      unfold transport
      rw [Arrow.inverse_composite]
      simp only [Arrow.comp_assoc]
    _ = transport C t R := by rw [hinner]; rfl

theorem transport_square (t : Arrow S A A) (R : Arrow S A B) :
    (transport C t R).comp C (transport C t R) = Arrow.id B :=
  Isotropy.square_one C B H (transport C t R)

def Dominant (A : Kernel S i) (t : Arrow S A A) : Prop :=
  ∀ (Z : Kernel S i), A < Z → ∀ x y, t.rel x y → Z.rel x y

omit H in
theorem transport_dominant (t : Arrow S A A) (ht : Dominant A t) (R : Arrow S A B) :
    Dominant B (transport C t R) := by
  intro Z hZ x y hxy
  let W := conjugate C R ⟨Z,hZ.le⟩
  have hW : A < W.val := (conjugate_strict C R ⟨Z,hZ.le⟩).mpr hZ
  have hle : ∀ a b, t.rel a b → W.val.rel a b := ht W.val hW
  have hh : TRel.comp (TRel.comp (TRel.converse R.rel) W.val.rel) R.rel x y := by
    obtain ⟨a,hax,b,hab,hby⟩ := hxy
    exact ⟨b,⟨a,hax,hle a b hab⟩,hby⟩
  change TRel.comp (TRel.comp (TRel.converse R.rel)
    (TRel.comp (TRel.comp R.rel Z.rel) (TRel.converse R.rel))) R.rel x y at hh
  rw [inverse_conjugation_rel R Z hZ.le] at hh
  exact hh

theorem transport_source_consumer (t : Arrow S A A) (ht : t ≠ Arrow.id A)
    (hd : Dominant A t) (R : Arrow S A B) :
    transport C t R ≠ Arrow.id B ∧
      (transport C t R).comp C (transport C t R) = Arrow.id B ∧
      Dominant B (transport C t R) ∧
      (∀ T : Arrow S A B, transport C t T = transport C t R) ∧
      ∀ q : B.Class, (transport C t R).quotientMap H q ≠ q := by
  have hn := transport_nonidentity C ht R
  exact ⟨hn,transport_square C H t R,transport_dominant C t hd R,
    fun T => transport_path_independent C H t T R,
    fun q => Arrow.nonidentity_fixed_point_free H _ hn q⟩

end CCO.RigidGroupoid.Geometry
