import CCO.Owners.Product.Induced
import CCO.Owners.Product.ActionConsumers
import Mathlib.Algebra.Group.Action.End

/-! The actual full fine-coloured product action survives an explicit
identification with an induced source carrier. Both the group and point
maps are retained, rather than just an abstract group isomorphism. -/

namespace CCO.Owners.Master
noncomputable section
open Product

variable {G K ED JC O U : Type*} [Group G]
variable [MulAction G K] [MulAction G ED] [MulAction G JC] [MulAction G O]
variable (P : ProductGeometry (G := G) (K := K) (ED := ED) (JC := JC) (O := O))
variable (D : Set ED) (C : Set JC) (B : Set O)
variable (hD : ∀ x : D, P.rD x.val ∈ B) (hC : ∀ x : C, P.rC x.val ∈ B)
variable (surjD : Function.Surjective (P.ownerD D B hD))
variable (surjC : Function.Surjective (P.ownerC C B hC))
variable (κ : U → K) (e : P.Carrier D C B hD hC ≃ U)
variable (point : ∀ x, κ (e x) = P.point D C B hD hC x)

local instance matching_action :
    MulAction (Matching (P.ownerActionD D B hD surjD) (P.ownerActionC C B hC surjC))
      (P.Carrier D C B hD hC) :=
  pullbackAction (P.ownerActionD D B hD surjD) (P.ownerActionC C B hC surjC)
    (P.ownerD D B hD) (P.ownerC C B hC)
    (fun g x => ((P.quotientOwnerD D B hD surjD).action_projection g x).symm)
    (fun g x => ((P.quotientOwnerC C B hC surjC).action_projection g x).symm)

def product_action_equivalence :
    letI := pullbackAction (P.ownerActionD D B hD surjD) (P.ownerActionC C B hC surjC)
      (P.ownerD D B hD) (P.ownerC C B hC)
      (fun g x => ((P.quotientOwnerD D B hD surjD).action_projection g x).symm)
      (fun g x => ((P.quotientOwnerC C B hC surjC).action_projection g x).symm)
    ActionEquivalence (OrbitalAut G K κ)
      (Matching (P.ownerActionD D B hD surjD) (P.ownerActionC C B hC surjC))
      U (P.Carrier D C B hD hC) := by
  letI := pullbackAction (P.ownerActionD D B hD surjD) (P.ownerActionC C B hC surjC)
    (P.ownerD D B hD) (P.ownerC C B hC)
    (fun g x => ((P.quotientOwnerD D B hD surjD).action_projection g x).symm)
    (fun g x => ((P.quotientOwnerC C B hC surjC).action_projection g x).symm)
  refine ⟨(orbitalAutCongr e point).symm.trans
    (P.fullAutEquiv D C B hD hC surjD surjC), e.symm, ?_⟩
  intro g x
  have he := (P.fullAutActionEquivalence D C B hD hC surjD surjC).equivariant
    ((orbitalAutCongr e point).symm g) (e.symm x)
  change ((orbitalAutCongr e point).symm g) • e.symm x =
    (P.fullAutEquiv D C B hD hC surjD surjC ((orbitalAutCongr e point).symm g)) • e.symm x at he
  change _ = (P.fullAutEquiv D C B hD hC surjD surjC
    ((orbitalAutCongr e point).symm g)) • e.symm x
  calc
    e.symm (g.val x) = ((orbitalAutCongr e point).symm g).val (e.symm x) := by
      change e.symm (g.val x) = e.symm (g.val (e (e.symm x)))
      rw [Equiv.apply_symm_apply]
    _ = _ := he

@[simp] theorem product_action_equivalence_point (x : U) :
    (product_action_equivalence P D C B hD hC surjD surjC κ e point).point x = e.symm x := rfl

@[simp] theorem product_action_equivalence_group (g : OrbitalAut G K κ) :
    (product_action_equivalence P D C B hD hC surjD surjC κ e point).group g =
      P.fullAutEquiv D C B hD hC surjD surjC ((orbitalAutCongr e point).symm g) := rfl

end
end CCO.Owners.Master
