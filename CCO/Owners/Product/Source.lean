import CCO.Owners.Product.SourceGeometry
import CCO.Owners.Product.SparseTransport
import CCO.Owners.Product.KernelConsumers
import CCO.Owners.Product.Boundary

/-! Actual finite exact-source exports: set fullness, full-colour group
identity and sparse-source EPPA with its separate finite consumer inputs.
There is no B018 owner provider, source EPPA or group section hidden here. -/
universe u v w t
namespace CCO.Owners.Product
open RawExact ExactCRT RawExact.CanonicalQuotients

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {G : Type t} [Group G] [∀ i, MulAction G (X i)]
variable (H : HomogeneousSource S G) (cco : SemanticCCO.{u,v,max u v,w} S)
variable {i : ι} (E F : ExactEq S H cco i)

local instance sourceInvariantE : Invariant G E.val := exactInvariant S H cco E
local instance sourceInvariantF : Invariant G F.val := exactInvariant S H cco F
local instance sourceInvariantK : Invariant G (E.val ⊓ F.val) := exactInvariant S H cco (E ⊓ F)
local instance sourceInvariantO : Invariant G (E.val ⊔ F.val) := exactInvariant S H cco (E ⊔ F)

variable (D : Set (Quotient E.val)) (C : Set (Quotient F.val))
variable (B : Set (Quotient (E.val ⊔ F.val)))
variable (hD : ∀ d : D, Abstract.quotientMap le_sup_left d.val ∈ B)
variable (hC : ∀ c : C, Abstract.quotientMap le_sup_right c.val ∈ B)
variable (surjD : Function.Surjective ((sourceGeometry S H cco E F).ownerD D B hD))
variable (surjC : Function.Surjective ((sourceGeometry S H cco E F).ownerC C B hC))

/-- Literal finite D,C determine a finite ACTUAL induced subset of X/K. -/
theorem actual_source_product_finite [Finite D] [Finite C] :
    Finite ((sourceGeometry S H cco E F).inducedCarrier D C) :=
  (sourceGeometry S H cco E F).inducedCarrier_finite D C

/-- C14–17 with every geometric provider discharged: literal quotients,
actual full induced W, named full original quotient orbitals and natural
coordinate restriction isomorphism. Equality remains in the fine readout. -/
noncomputable def actual_source_product_aut :
    OrbitalAut G (Quotient (E.val ⊓ F.val))
      (Subtype.val : (sourceGeometry S H cco E F).inducedCarrier D C → _) ≃*
      Matching ((sourceGeometry S H cco E F).ownerActionD D B hD surjD)
        ((sourceGeometry S H cco E F).ownerActionC C B hC surjC) :=
  (sourceGeometry S H cco E F).actualInducedAutEquiv D C B hD hC surjD surjC

/-- C23–26 on the actual ORIGINAL sparse induced subset. The displayed
coordinate sets are the true projections of that same a, read through the
proved natural coordinate equivalence. A11 is separate from target kernels. -/
theorem actual_source_product_eppa
    (surjD : Function.Surjective ((sourceGeometry S H cco E F).ownerD D B hD))
    (a : Set ((sourceGeometry S H cco E F).inducedCarrier D C))
    (first : EPPAFor (G := G) (ι := (Subtype.val : D → Quotient E.val))
      ((fun w : (sourceGeometry S H cco E F).Carrier D C B hD hC => w.val.1) ''
        (((sourceGeometry S H cco E F).pointCarrierEquiv D C B hD hC) ⁻¹' a)))
    (second : PrescribedEPPAFor ((sourceGeometry S H cco E F).quotientOwnerC C B hC surjC)
      ((fun w : (sourceGeometry S H cco E F).Carrier D C B hD hC => w.val.2) ''
        (((sourceGeometry S H cco E F).pointCarrierEquiv D C B hD hC) ⁻¹' a))) :
    EPPAFor (G := G) (ι := (Subtype.val : (sourceGeometry S H cco E F).inducedCarrier D C → _)) a :=
  (sourceGeometry S H cco E F).actual_eppa_full_product D C B hD hC surjC surjD a first second



/-- The full fine-coloured ACTUAL source action has the nonnested target
kernel property under exactly A13/A14. The source FPA is discharged above;
no map from the prescribed target to the owner set is supplied. -/
theorem actual_source_target_kernel {GT T : Type*} [Group GT] [MulAction GT T]
    [Nonempty ((sourceGeometry S H cco E F).Carrier D C B hD hC)]
    (τ : OrbitalAut G (Quotient E.val) (Subtype.val : D → Quotient E.val) →* GT)
    (t : D → T) (eqT : ∀ g x, t (g • x) = τ g • t x)
    (surjT : Function.Surjective t)
    (first : Function.Surjective τ ∧ GroupActions.FibreTransitive τ t)
    (second : GroupActions.PrescribedLift ((sourceGeometry S H cco E F).ownerActionC C B hC surjC) ((sourceGeometry S H cco E F).ownerC C B hC)) :
    Function.Surjective
      ((matchingTarget ((sourceGeometry S H cco E F).ownerActionD D B hD surjD) ((sourceGeometry S H cco E F).ownerActionC C B hC surjC) τ).comp
        ((sourceGeometry S H cco E F).fullAutEquiv D C B hD hC surjD surjC).toMonoidHom) ∧
    GroupActions.FibreTransitive
      ((matchingTarget ((sourceGeometry S H cco E F).ownerActionD D B hD surjD) ((sourceGeometry S H cco E F).ownerActionC C B hC surjC) τ).comp
        ((sourceGeometry S H cco E F).fullAutEquiv D C B hD hC surjD surjC).toMonoidHom)
      (fun w : (sourceGeometry S H cco E F).Carrier D C B hD hC => t w.val.1) :=
  (sourceGeometry S H cco E F).actual_nonnested_from_kernel D C B hD hC surjD surjC τ t eqT surjT first second

end CCO.Owners.Product
