import CCO.Owners.Product.SparseEPPA
import CCO.Owners.Product.Induced

/-! Sparse partial maps are transported through the proved actual induced
set equivalence, without completing their domains to full products. -/
namespace CCO.Owners.Product
variable {G A U V : Type*} [Group G] [MulAction G A]
variable {ι : U → A} {κ : V → A}

noncomputable def OrbitalPartial.pullback (e : U ≃ V) (h : ∀ u, κ (e u) = ι u)
    (p : OrbitalPartial (G := G) κ) : OrbitalPartial (G := G) ι where
  domain := e ⁻¹' p.domain
  map x := e.symm (p.map ⟨e x.val,x.property⟩)
  injective := by
    intro x y hxy
    apply Subtype.ext
    apply e.injective
    exact congrArg Subtype.val (p.injective (e.symm.injective hxy))
  pair x y := by
    have hb : ∀ v, κ v = ι (e.symm v) := fun v => by simpa using h (e.symm v)
    have hp := p.pair ⟨e x.val,x.property⟩ ⟨e y.val,y.property⟩
    simpa only [hb,Equiv.symm_apply_apply] using hp

/-- Ordinary EPPA is invariant under this actual induced-structure
isomorphism; the map being extended is still the original sparse map. -/
theorem eppa_congr (e : U ≃ V) (h : ∀ u, κ (e u) = ι u) (a : Set V)
    (ep : EPPAFor (G := G) (ι := ι) (e ⁻¹' a)) :
    EPPAFor (G := G) (ι := κ) a := by
  intro p hdom hmap
  let q := p.pullback e h
  have qdom : q.domain ⊆ e ⁻¹' a := fun x hx => hdom hx
  have qmap : ∀ x, q.map x ∈ e ⁻¹' a := by
    intro x
    change e (e.symm (p.map ⟨e x.val,x.property⟩)) ∈ a
    rw [Equiv.apply_symm_apply]
    exact hmap _
  obtain ⟨g,hg⟩ := ep q qdom qmap
  refine ⟨orbitalAutCongr e h g,?_⟩
  intro v
  let u : q.domain := ⟨e.symm v.val,by
    change e (e.symm v.val) ∈ p.domain
    simpa only [Equiv.apply_symm_apply] using v.property⟩
  have hu : q.map u = e.symm (p.map v) := by
    change e.symm (p.map ⟨e (e.symm v.val),_⟩) = e.symm (p.map v)
    congr 1
    apply congrArg p.map
    exact Subtype.ext (e.apply_symm_apply _)
  change e (g.val (e.symm v.val)) = p.map v
  calc
    _ = e (q.map u) := congrArg e (hg u)
    _ = e (e.symm (p.map v)) := congrArg e hu
    _ = _ := e.apply_symm_apply _

namespace ProductGeometry
variable {K ED JC O : Type*}
variable [MulAction G K] [MulAction G ED] [MulAction G JC] [MulAction G O]
variable (P : ProductGeometry (G := G) (K := K) (ED := ED) (JC := JC) (O := O))
variable (D : Set ED) (C : Set JC) (B : Set O)
variable (hD : ∀ x : D, P.rD x.val ∈ B) (hC : ∀ x : C, P.rC x.val ∈ B)
variable (surjD : Function.Surjective (P.ownerD D B hD))
variable (surjC : Function.Surjective (P.ownerC C B hC))

/-- C26 on literal actual original induced W. Coordinate images below
are EXACTLY those of the same sparse a, via the proved natural bijection. -/
theorem actual_eppa_full_product
    (surjD : Function.Surjective (P.ownerD D B hD))
    (a : Set (P.inducedCarrier D C))
    (first : EPPAFor (G := G) (ι := (Subtype.val : D → ED))
      ((fun w : P.Carrier D C B hD hC => w.val.1) ''
        ((P.pointCarrierEquiv D C B hD hC) ⁻¹' a)))
    (second : PrescribedEPPAFor (P.quotientOwnerC C B hC surjC)
      ((fun w : P.Carrier D C B hD hC => w.val.2) ''
        ((P.pointCarrierEquiv D C B hD hC) ⁻¹' a))) :
    EPPAFor (G := G) (ι := (Subtype.val : P.inducedCarrier D C → K)) a := by
  apply eppa_congr (P.pointCarrierEquiv D C B hD hC) (fun _ => rfl) a
  exact P.eppa_full_product D C B hD hC surjC surjD _ first second

end ProductGeometry
end CCO.Owners.Product
