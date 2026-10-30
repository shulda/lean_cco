import CCO.Owners.Product.Induced
import CCO.Owners.Product.ActionConsumers
import Mathlib.Logic.Equiv.Set

/-! Literal equivariant identifications preserve the complete orbital
language and the FULL automorphism groups of induced subsets. No global
automorphism-lifting or choice of a group section is required. -/

namespace CCO.RankInduction
noncomputable section
open Owners.Product

variable {G A B U V : Type*} [Group G] [MulAction G A] [MulAction G B]

theorem equivariant_symm (e : A ≃ B)
    (he : ∀ (g : G) a, e (g • a) = g • e a) (g : G) (b : B) :
    e.symm (g • b) = g • e.symm b := by
  apply e.injective
  rw [Equiv.apply_symm_apply, he, Equiv.apply_symm_apply]

theorem orbital_iff (e : A ≃ B)
    (he : ∀ (g : G) a, e (g • a) = g • e a) (a b x y : A) :
    GroupActions.orbital (G := G) a b x y ↔
      GroupActions.orbital (G := G) (e a) (e b) (e x) (e y) := by
  constructor
  · rintro ⟨g, hx, hy⟩
    exact ⟨g, (he g a).symm.trans (congrArg e hx),
      (he g b).symm.trans (congrArg e hy)⟩
  · rintro ⟨g, hx, hy⟩
    exact ⟨g, e.injective ((he g a).trans hx),
      e.injective ((he g b).trans hy)⟩

variable {ι : U → A} {κ : V → B}

def fullAutHomOf (e : A ≃ B)
    (he : ∀ (g : G) a, e (g • a) = g • e a)
    (E : U ≃ V) (hE : ∀ u, κ (E u) = e (ι u)) :
    OrbitalAut G A ι →* OrbitalAut G B κ where
  toFun f := ⟨E.permCongr f.val, (mem_orbitalAut_iff _).mpr (by
    intro x y
    have hb : ∀ v, κ v = e (ι (E.symm v)) := fun v => by
      simpa only [Equiv.apply_symm_apply] using hE (E.symm v)
    simpa only [Equiv.permCongr_apply, hb, Equiv.symm_apply_apply] using
      (orbital_iff e he _ _ _ _).mp (orbitalAut_pair f (E.symm x) (E.symm y)))⟩
  map_one' := by
    apply Subtype.ext
    apply Equiv.ext
    intro x
    exact E.apply_symm_apply x
  map_mul' f k := by
    apply Subtype.ext
    apply Equiv.ext
    intro x
    change E (f.val (k.val (E.symm x))) = E (f.val (E.symm (E (k.val (E.symm x)))))
    rw [Equiv.symm_apply_apply]

def fullAutEquivOf (e : A ≃ B)
    (he : ∀ (g : G) a, e (g • a) = g • e a)
    (E : U ≃ V) (hE : ∀ u, κ (E u) = e (ι u)) :
    OrbitalAut G A ι ≃* OrbitalAut G B κ where
  toFun := fullAutHomOf e he E hE
  invFun := fullAutHomOf e.symm (equivariant_symm e he) E.symm (by
    intro v
    apply e.injective
    rw [Equiv.apply_symm_apply]
    exact (hE (E.symm v)).symm.trans (congrArg κ (E.apply_symm_apply v)))
  left_inv f := by
    apply Subtype.ext
    apply Equiv.ext
    intro x
    change E.symm (E (f.val (E.symm (E x)))) = f.val x
    simp only [Equiv.symm_apply_apply]
  right_inv f := by
    apply Subtype.ext
    apply Equiv.ext
    intro x
    change E (E.symm (f.val (E (E.symm x)))) = f.val x
    simp only [Equiv.apply_symm_apply]
  map_mul' := (fullAutHomOf e he E hE).map_mul

@[simp] theorem fullAutEquivOf_apply (e : A ≃ B)
    (he : ∀ (g : G) a, e (g • a) = g • e a)
    (E : U ≃ V) (hE : ∀ u, κ (E u) = e (ι u))
    (f : OrbitalAut G A ι) (u : U) :
    (fullAutEquivOf e he E hE f).val (E u) = E (f.val u) := by
  change E (f.val (E.symm (E u))) = E (f.val u)
  rw [Equiv.symm_apply_apply]

def subimageEquiv (e : A ≃ B) (D : Set A) : D ≃ (e '' D) :=
  Equiv.Set.image e D e.injective

@[simp] theorem subimageEquiv_val (e : A ≃ B) (D : Set A) (x : D) :
    (subimageEquiv e D x).val = e x.val := rfl

def fullAutEquiv (e : A ≃ B)
    (he : ∀ (g : G) a, e (g • a) = g • e a) (D : Set A) :
    OrbitalAut G A (Subtype.val : D → A) ≃*
      OrbitalAut G B (Subtype.val : (e '' D) → B) :=
  fullAutEquivOf e he (subimageEquiv e D) (fun _ => rfl)

@[simp] theorem fullAutEquiv_apply (e : A ≃ B)
    (he : ∀ (g : G) a, e (g • a) = g • e a) (D : Set A)
    (f : OrbitalAut G A (Subtype.val : D → A)) (x : D) :
    (fullAutEquiv e he D f).val (subimageEquiv e D x) =
      subimageEquiv e D (f.val x) := fullAutEquivOf_apply e he _ _ f x

def fullActionEquivalenceOf (e : A ≃ B)
    (he : ∀ (g : G) a, e (g • a) = g • e a)
    (E : U ≃ V) (hE : ∀ u, κ (E u) = e (ι u)) :
    ActionEquivalence (OrbitalAut G A ι) (OrbitalAut G B κ) U V where
  group := fullAutEquivOf e he E hE
  point := E
  equivariant f x := (fullAutEquivOf_apply e he E hE f x).symm

end
end CCO.RankInduction
