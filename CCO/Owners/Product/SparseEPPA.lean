import CCO.Owners.Product.FullAutomorphisms
import CCO.Owners.Product.SparseDescent

/-! Sparse-source EPPA is independent of either auxiliary target kernel.
The first extension supplies its ENTIRE actual owner action; the second
extension is requested with exactly that action on ALL owners. -/
namespace CCO.Owners.Product.ProductGeometry
variable {G K ED JC O : Type*} [Group G]
variable [MulAction G K] [MulAction G ED] [MulAction G JC] [MulAction G O]
variable (P : ProductGeometry (G := G) (K := K) (ED := ED) (JC := JC) (O := O))
variable (D : Set ED) (C : Set JC) (B : Set O)
variable (hD : ∀ x : D, P.rD x.val ∈ B) (hC : ∀ x : C, P.rC x.val ∈ B)
variable (surjD : Function.Surjective (P.ownerD D B hD))
variable (surjC : Function.Surjective (P.ownerC C B hC))

/-- C23–24/26: every genuine sparse ORIGINAL partial isomorphism extends.
No fullness is imposed on a, no target T is used, and no point-homogeneity
hypothesis is needed in this independent EPPA consumer. -/
theorem eppa_full_product (surjD : Function.Surjective (P.ownerD D B hD)) (a : Set (P.Carrier D C B hD hC))
    (first : EPPAFor (G := G) (ι := (Subtype.val : D → ED))
      ((fun w : P.Carrier D C B hD hC => w.val.1) '' a))
    (second : PrescribedEPPAFor (P.quotientOwnerC C B hC surjC)
      ((fun w : P.Carrier D C B hD hC => w.val.2) '' a)) :
    EPPAFor (G := G) (ι := P.point D C B hD hC) a := by
  let QD := P.quotientD D C B hD hC surjC
  let QC := P.quotientC D C B hD hC surjD
  let OD := P.quotientOwnerD D B hD surjD
  let OC := P.quotientOwnerC C B hC surjC
  intro p hdom hmap
  obtain ⟨g,hg⟩ := first (QD.projectedPartial p)
    (QD.partial_domain_subset p hdom) (QD.partial_mapsTo p hmap)
  let δ := OD.action g
  have compatible : ∀ x : (QC.projectedPartial p).domain,
      OC.projection ((QC.projectedPartial p).map x) = δ.val (OC.projection x.val) := by
    intro x
    obtain ⟨w,hw,hwx⟩ := x.property
    let w' : p.domain := ⟨w,hw⟩
    have hx : x = ⟨QC.projection w,⟨w,hw,rfl⟩⟩ := Subtype.ext hwx.symm
    subst x
    rw [QC.partial_projection p w']
    change P.ownerC C B hC (p.map w').val.2 = δ.val (P.ownerC C B hC w.val.2)
    calc
      _ = P.ownerD D B hD (p.map w').val.1 := (p.map w').property.symm
      _ = P.ownerD D B hD ((QD.projectedPartial p).map
          ⟨QD.projection w,⟨w,hw,rfl⟩⟩) :=
        congrArg (P.ownerD D B hD) (QD.partial_projection p w').symm
      _ = P.ownerD D B hD (g.val w.val.1) :=
        congrArg (P.ownerD D B hD) (hg _).symm
      _ = δ.val (P.ownerD D B hD w.val.1) := (OD.action_projection g w.val.1).symm
      _ = _ := congrArg δ.val w.property
  obtain ⟨h,hh,hhδ⟩ := second (QC.projectedPartial p)
    (QC.partial_domain_subset p hdom) (QC.partial_mapsTo p hmap) δ compatible
  let k : Matching (P.ownerActionD D B hD surjD) (P.ownerActionC C B hC surjC) :=
    ⟨(g,h),hhδ.symm⟩
  refine ⟨P.lift D C B hD hC surjD surjC k,?_⟩
  intro w
  apply Subtype.ext
  apply Prod.ext
  · change g.val w.val.val.1 = (p.map w).val.1
    exact (hg _).trans (QD.partial_projection p w)
  · change h.val w.val.val.2 = (p.map w).val.2
    exact (hh _).trans (QC.partial_projection p w)

end CCO.Owners.Product.ProductGeometry
