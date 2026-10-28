import CCO.Owners.Product.Descent
import CCO.Owners.Product.Matching
import Mathlib.Algebra.Group.Action.End

/-! Conditional geometric calculus of a full fine-coloured product. The
source instance below constructs every geometric field from actual exact
quotients; the subsequent abstract action lemmas do not consume this data. -/
namespace CCO.Owners.Product

variable {G K ED JC O : Type*} [Group G]
variable [MulAction G K] [MulAction G ED] [MulAction G JC] [MulAction G O]

structure ProductGeometry where
  pD : K → ED
  pC : K → JC
  rD : ED → O
  rC : JC → O
  equiv_pD : ∀ (g : G) x, pD (g • x) = g • pD x
  equiv_pC : ∀ (g : G) x, pC (g • x) = g • pC x
  equiv_rD : ∀ (g : G) x, rD (g • x) = g • rD x
  equiv_rC : ∀ (g : G) x, rC (g • x) = g • rC x
  full : K ≃ Pullback rD rC
  full_fst : ∀ x, (full x).val.1 = pD x
  full_snd : ∀ x, (full x).val.2 = pC x
  fine : ∀ a b x y,
    (GroupActions.orbital (G := G) (pD a) (pD b) (pD x) (pD y) ∧
      GroupActions.orbital (G := G) (pC a) (pC b) (pC x) (pC y)) ↔
      GroupActions.orbital (G := G) a b x y

namespace ProductGeometry
variable (P : ProductGeometry (G := G) (K := K) (ED := ED) (JC := JC) (O := O))
variable (D : Set ED) (C : Set JC) (B : Set O)
variable (hD : ∀ x : D, P.rD x.val ∈ B) (hC : ∀ x : C, P.rC x.val ∈ B)

def ownerD (x : D) : B := ⟨P.rD x.val,hD x⟩
def ownerC (x : C) : B := ⟨P.rC x.val,hC x⟩
abbrev Carrier := Pullback (P.ownerD D B hD) (P.ownerC C B hC)

noncomputable def point (w : P.Carrier D C B hD hC) : K :=
  P.full.symm ⟨(w.val.1.val,w.val.2.val),congrArg Subtype.val w.property⟩

@[simp] theorem pD_point (w : P.Carrier D C B hD hC) :
    P.pD (P.point D C B hD hC w) = w.val.1.val := by
  simpa only [point,Equiv.apply_symm_apply] using
    (P.full_fst (P.point D C B hD hC w)).symm
@[simp] theorem pC_point (w : P.Carrier D C B hD hC) :
    P.pC (P.point D C B hD hC w) = w.val.2.val := by
  simpa only [point,Equiv.apply_symm_apply] using
    (P.full_snd (P.point D C B hD hC w)).symm

theorem point_injective : Function.Injective (P.point D C B hD hC) := by
  intro w v h
  apply Subtype.ext
  apply Prod.ext
  · apply Subtype.ext
    exact (P.pD_point D C B hD hC w).symm.trans
      ((congrArg P.pD h).trans (P.pD_point D C B hD hC v))
  · apply Subtype.ext
    exact (P.pC_point D C B hD hC w).symm.trans
      ((congrArg P.pC h).trans (P.pC_point D C B hD hC v))

variable (surjD : Function.Surjective (P.ownerD D B hD))
variable (surjC : Function.Surjective (P.ownerC C B hC))

def quotientD : OrbitalQuotient (G := G) (P.point D C B hD hC) (Subtype.val : D → ED) where
  ambient := P.pD
  equivariant := P.equiv_pD
  projection := fun w => w.val.1
  surjective := pullback_fst_surjective _ _ surjC
  target_injective := Subtype.val_injective
  commutes w := (P.pD_point D C B hD hC w).symm

def quotientC : OrbitalQuotient (G := G) (P.point D C B hD hC) (Subtype.val : C → JC) where
  ambient := P.pC
  equivariant := P.equiv_pC
  projection := fun w => w.val.2
  surjective := pullback_snd_surjective _ _ surjD
  target_injective := Subtype.val_injective
  commutes w := (P.pC_point D C B hD hC w).symm

def quotientOwnerD : OrbitalQuotient (G := G) (Subtype.val : D → ED) (Subtype.val : B → O) where
  ambient := P.rD
  equivariant := P.equiv_rD
  projection := P.ownerD D B hD
  surjective := surjD
  target_injective := Subtype.val_injective
  commutes _ := rfl

def quotientOwnerC : OrbitalQuotient (G := G) (Subtype.val : C → JC) (Subtype.val : B → O) where
  ambient := P.rC
  equivariant := P.equiv_rC
  projection := P.ownerC C B hC
  surjective := surjC
  target_injective := Subtype.val_injective
  commutes _ := rfl

end ProductGeometry
end CCO.Owners.Product
