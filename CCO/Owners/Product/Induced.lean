import CCO.Owners.Product.FullAutomorphisms
import Mathlib.Basic.Finite.Prod

/-! The full product really is an actual induced original quotient subset.
This equivalence transports its FULL structural automorphism group. -/
namespace CCO.Owners.Product
variable {G A U V : Type*} [Group G] [MulAction G A]

noncomputable def orbitalAutCongrHom {ι : U → A} {κ : V → A}
    (e : U ≃ V) (h : ∀ x, κ (e x) = ι x) :
    OrbitalAut G A ι →* OrbitalAut G A κ where
  toFun g := ⟨e.permCongr g.val, (mem_orbitalAut_iff _).mpr (by
    intro x y
    have hb : ∀ v, κ v = ι (e.symm v) := fun v => by simpa using h (e.symm v)
    simpa only [Equiv.permCongr_apply,hb,Equiv.symm_apply_apply] using
      orbitalAut_pair g (e.symm x) (e.symm y))⟩
  map_one' := by
    apply Subtype.ext
    apply Equiv.ext
    intro x
    exact e.apply_symm_apply x
  map_mul' g k := by
    apply Subtype.ext
    apply Equiv.ext
    intro x
    change e (g.val (k.val (e.symm x))) = e (g.val (e.symm (e (k.val (e.symm x)))))
    rw [Equiv.symm_apply_apply]

noncomputable def orbitalAutCongr {ι : U → A} {κ : V → A}
    (e : U ≃ V) (h : ∀ x, κ (e x) = ι x) :
    OrbitalAut G A ι ≃* OrbitalAut G A κ where
  toFun := orbitalAutCongrHom e h
  invFun := orbitalAutCongrHom e.symm (fun y => by simpa using (h (e.symm y)).symm)
  left_inv g := by
    apply Subtype.ext
    apply Equiv.ext
    intro x
    change e.symm (e (g.val (e.symm (e x)))) = g.val x
    simp only [Equiv.symm_apply_apply]
  right_inv g := by
    apply Subtype.ext
    apply Equiv.ext
    intro x
    change e (e.symm (g.val (e (e.symm x)))) = g.val x
    simp only [Equiv.apply_symm_apply]
  map_mul' := (orbitalAutCongrHom e h).map_mul

namespace ProductGeometry
variable {K ED JC O : Type*}
variable [MulAction G K] [MulAction G ED] [MulAction G JC] [MulAction G O]
variable (P : ProductGeometry (G := G) (K := K) (ED := ED) (JC := JC) (O := O))
variable (D : Set ED) (C : Set JC) (B : Set O)
variable (hD : ∀ x : D, P.rD x.val ∈ B) (hC : ∀ x : C, P.rC x.val ∈ B)

/-- The ACTUAL original fine quotient points above the two displayed sets. -/
def inducedCarrier : Set K := {x | P.pD x ∈ D ∧ P.pC x ∈ C}

noncomputable def pointCarrierEquiv :
    P.Carrier D C B hD hC ≃ P.inducedCarrier D C where
  toFun w := ⟨P.point D C B hD hC w,by
    change P.pD (P.point D C B hD hC w) ∈ D ∧ P.pC (P.point D C B hD hC w) ∈ C
    rw [P.pD_point,P.pC_point]
    exact ⟨w.val.1.property,w.val.2.property⟩⟩
  invFun x := ⟨(⟨P.pD x.val,x.property.1⟩,⟨P.pC x.val,x.property.2⟩),by
    apply Subtype.ext
    change P.rD (P.pD x.val) = P.rC (P.pC x.val)
    simpa only [P.full_fst,P.full_snd] using (P.full x.val).property⟩
  left_inv w := by
    apply Subtype.ext
    apply Prod.ext
    · apply Subtype.ext
      exact P.pD_point D C B hD hC w
    · apply Subtype.ext
      exact P.pC_point D C B hD hC w
  right_inv x := by
    apply Subtype.ext
    apply P.full.injective
    apply Subtype.ext
    apply Prod.ext
    · simpa only [point,Equiv.apply_symm_apply] using (P.full_fst x.val).symm
    · simpa only [point,Equiv.apply_symm_apply] using (P.full_snd x.val).symm

@[simp] theorem pointCarrierEquiv_val (w : P.Carrier D C B hD hC) :
    (P.pointCarrierEquiv D C B hD hC w).val = P.point D C B hD hC w := rfl

/-- Finiteness concerns the true induced class, never Nat.card of an
unproved-finite carrier. Fullness identifies it with the finite set product. -/
theorem inducedCarrier_finite [Finite D] [Finite C] : Finite (P.inducedCarrier D C) :=
  Finite.of_surjective (P.pointCarrierEquiv D C Set.univ (fun _ => trivial) (fun _ => trivial))
    (Equiv.surjective _)

/-- C17 on the ACTUAL induced subset of the fine original quotient. -/
noncomputable def actualInducedAutEquiv
    (surjD : Function.Surjective (P.ownerD D B hD))
    (surjC : Function.Surjective (P.ownerC C B hC)) :
    OrbitalAut G K (Subtype.val : P.inducedCarrier D C → K) ≃*
      Matching (P.ownerActionD D B hD surjD) (P.ownerActionC C B hC surjC) :=
  (orbitalAutCongr (P.pointCarrierEquiv D C B hD hC) (fun _ => rfl)).symm.trans
    (P.fullAutEquiv D C B hD hC surjD surjC)

end ProductGeometry
end CCO.Owners.Product
