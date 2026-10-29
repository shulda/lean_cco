import CCO.Owners.Joint.ActualGeometry
import CCO.Owners.Joint.Induced
import CCO.Owners.Joint.SparseEPPA
import CCO.Owners.Product.SparseTransport

/-! C22: the complete actual-source export. Every ambient geometric field
comes from actual exact quotients, actual finite CRT and independent RAW
fine-colour readout. Point and sparse EPPA inputs remain separate. -/
universe u v w t z
namespace CCO.Owners.Joint.Actual
open CCO.Owners.Product
open RawExact ExactCRT RawExact.CanonicalQuotients
variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {G : Type t} [Group G] [∀ j, MulAction G (X j)]
variable (H : HomogeneousSource S G) (cco : SemanticCCO.{u,v,max u v,w} S)
variable {i : ι} {I : Type z} [Finite I] [Nonempty I]
variable (C T : I → ExactEq S H cco i) (hCT : ∀ k, C k ≤ T k)
variable (meet_id : ∀ x y : X i, (∀ k, (C k).val x y) → x = y)
variable (gate : ∀ k l, k ≠ l → (C k).val ⊔ (C l).val = (T k).val ⊔ (T l).val)
local instance invariantC (k : I) : Invariant G (C k).val := Product.exactInvariant S H cco (C k)
local instance invariantT (k : I) : Invariant G (T k).val := Product.exactInvariant S H cco (T k)

variable (B : Set (Quotient (Abstract.familyMeet (fun k => (T k).val))))
variable (D : ∀ k, Set (Quotient (C k).val))
variable (hD : ∀ k (d : D k), (actualGeometry S H cco C T hCT meet_id gate).own k d.val ∈ (actualGeometry S H cco C T hCT meet_id gate).OwnerImage B k)
variable (surjD : ∀ k, Function.Surjective ((actualGeometry S H cco C T hCT meet_id gate).finiteOwn B D hD k))
variable (fullB : FullOwners ((actualGeometry S H cco C T hCT meet_id gate).finiteDiagram B))

/-- The declared full tuple carrier is literally a finite induced subset
of the ORIGINAL source, including repeated and identity coordinates. -/
theorem finite_real_witness [∀ k, Finite (D k)] : Finite ((actualGeometry S H cco C T hCT meet_id gate).inducedCarrier D) :=
  (actualGeometry S H cco C T hCT meet_id gate).inducedCarrier_finite D

/-- The WHOLE original induced automorphism group has the boxed JWA
identity. A tuple's common owner is unique, with no section chosen. -/
noncomputable def full_automorphisms :
    OrbitalAut G (X i) (Subtype.val : (actualGeometry S H cco C T hCT meet_id gate).inducedCarrier D → X i) ≃*
      Matching ((actualGeometry S H cco C T hCT meet_id gate).factorAction B D hD surjD) ((actualGeometry S H cco C T hCT meet_id gate).jointAction B) :=
  (actualGeometry S H cco C T hCT meet_id gate).actualInducedAutEquiv B D hD surjD fullB

/-- The source's existential coordinate-only version of JWA. -/
noncomputable def full_coordinate_automorphisms :
    OrbitalAut G (X i) (Subtype.val : (actualGeometry S H cco C T hCT meet_id gate).inducedCarrier D → X i) ≃*
      ↥(coordinateGroup ((actualGeometry S H cco C T hCT meet_id gate).factorAction B D hD surjD) ((actualGeometry S H cco C T hCT meet_id gate).jointAction B)) :=
  (full_automorphisms S H cco C T hCT meet_id gate B D hD surjD fullB).trans
    (matchingCoordinatesEquiv ((actualGeometry S H cco C T hCT meet_id gate).factorAction B D hD surjD) ((actualGeometry S H cco C T hCT meet_id gate).jointAction B)
      ((actualGeometry S H cco C T hCT meet_id gate).jointAction_injective B))

/-- Every factor projection is onto its ENTIRE displayed finite D_k. -/
theorem coordinate_onto (k : I) :
    Function.Surjective ((actualGeometry S H cco C T hCT meet_id gate).inducedCoordinateQuotient B D hD surjD k).projection :=
  ((actualGeometry S H cco C T hCT meet_id gate).inducedCoordinateQuotient B D hD surjD k).surjective

include hD surjD fullB
/-- Every joint owner is reached, and no extra compatible owner is
introduced. This is equality of actual ambient set images. -/
theorem owner_image :
    (actualGeometry S H cco C T hCT meet_id gate).joint '' (actualGeometry S H cco C T hCT meet_id gate).inducedCarrier D = B := by
  ext b
  constructor
  · rintro ⟨x,hx,rfl⟩
    let x' : (actualGeometry S H cco C T hCT meet_id gate).inducedCarrier D := ⟨x,hx⟩
    have h := ((actualGeometry S H cco C T hCT meet_id gate).inducedOwnerQuotient B D hD surjD fullB).commutes x'
    change (((actualGeometry S H cco C T hCT meet_id gate).inducedOwnerQuotient B D hD surjD fullB).projection x').val =
      (actualGeometry S H cco C T hCT meet_id gate).joint x at h
    rw [← h]
    exact (((actualGeometry S H cco C T hCT meet_id gate).inducedOwnerQuotient B D hD surjD fullB).projection x').property
  · intro hb
    obtain ⟨x,hx⟩ := ((actualGeometry S H cco C T hCT meet_id gate).inducedOwnerQuotient B D hD surjD fullB).surjective ⟨b,hb⟩
    refine ⟨x.val,x.property,?_⟩
    exact (((actualGeometry S H cco C T hCT meet_id gate).inducedOwnerQuotient B D hD surjD fullB).commutes x).symm.trans
      (congrArg Subtype.val hx)

variable [sourceCountable : Countable (X i)]
include sourceCountable

/-- Every prescribed ENTIRE full joint-owner action lifts with every
compatible original point motion. Current actual-source scope retains
countability; the abstract finite theorems do not require it. -/
theorem prescribed_point
    (factorLift : ∀ k, GroupActions.PrescribedLift
      ((actualGeometry S H cco C T hCT meet_id gate).factorAction B D hD surjD k) ((actualGeometry S H cco C T hCT meet_id gate).finiteOwn B D hD k)) :
    GroupActions.PrescribedLift ((actualGeometry S H cco C T hCT meet_id gate).inducedOwnerQuotient B D hD surjD fullB).action
      ((actualGeometry S H cco C T hCT meet_id gate).inducedOwnerQuotient B D hD surjD fullB).projection :=
  (actualGeometry S H cco C T hCT meet_id gate).actual_prescribed_point B D hD surjD fullB factorLift

/-- Onto FULL finite owner action and transitive kernel on every fibre,
including the direct empty-system branch. -/
theorem onto_and_kernel
    (factorLift : ∀ k, GroupActions.PrescribedLift
      ((actualGeometry S H cco C T hCT meet_id gate).factorAction B D hD surjD k) ((actualGeometry S H cco C T hCT meet_id gate).finiteOwn B D hD k)) :
    Function.Surjective ((actualGeometry S H cco C T hCT meet_id gate).inducedOwnerQuotient B D hD surjD fullB).action ∧
      GroupActions.FibreTransitive ((actualGeometry S H cco C T hCT meet_id gate).inducedOwnerQuotient B D hD surjD fullB).action
        ((actualGeometry S H cco C T hCT meet_id gate).inducedOwnerQuotient B D hD surjD fullB).projection :=
  (actualGeometry S H cco C T hCT meet_id gate).actual_onto_and_kernel B D hD surjD fullB factorLift

/-- The independent optional EPPA clause applies to the ORIGINAL sparse
input a, with its precise images. It imports no point-motion hypothesis. -/
theorem eppa_sparse (a : Set ((actualGeometry S H cco C T hCT meet_id gate).inducedCarrier D))
    (ownerEPPA : EPPAFor (G := G) (ι := (Subtype.val : B → _))
      (((actualGeometry S H cco C T hCT meet_id gate).ownerQuotient B D hD surjD fullB).projection ''
        (((actualGeometry S H cco C T hCT meet_id gate).pointCarrierEquiv B D hD) ⁻¹' a)))
    (factorEPPA : ∀ k, PrescribedEPPAFor ((actualGeometry S H cco C T hCT meet_id gate).factorOwnerQuotient B D hD surjD k)
      ((fun w : (actualGeometry S H cco C T hCT meet_id gate).Witness B D hD => w.val k) ''
        (((actualGeometry S H cco C T hCT meet_id gate).pointCarrierEquiv B D hD) ⁻¹' a))) :
    EPPAFor (G := G) (ι := (Subtype.val : (actualGeometry S H cco C T hCT meet_id gate).inducedCarrier D → X i)) a := by
  apply eppa_congr ((actualGeometry S H cco C T hCT meet_id gate).pointCarrierEquiv B D hD) (fun _ => rfl) a
  exact (actualGeometry S H cco C T hCT meet_id gate).eppa_sparse B D hD surjD fullB _ ownerEPPA factorEPPA

end CCO.Owners.Joint.Actual

