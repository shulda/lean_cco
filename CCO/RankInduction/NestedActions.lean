import CCO.RankInduction.NestedOwners
import CCO.Owners.Master.ActionNaturality

/-! M3 transports to the natural actions on the ENTIRE original quotient
images. Both point maps and full group maps commute; an abstract group
isomorphism alone is never substituted for the natural restriction. -/

universe v w t
namespace CCO.RankInduction.Factors
noncomputable section
open RawExact ExactCRT CanonicalQuotients Owners.Product Owners.Provider Owners.Master

def reverseAction {K L X Y : Type*} [Group K] [Group L]
    [MulAction K X] [MulAction L Y] (E : ActionEquivalence K L X Y) :
    ActionEquivalence L K Y X where
  group := E.group.symm
  point := E.point.symm
  equivariant g x := by
    apply E.point.injective
    rw [Equiv.apply_symm_apply, E.equivariant,
      MulEquiv.apply_symm_apply, Equiv.apply_symm_apply]

variable {M : Type v} (S : AtomicSource.{0,v,w} Unit (fun _ => M))
variable {G : Type t} [Group G] [MulAction G M] [Countable M]
variable (H : HomogeneousSource S G) (cco : SemanticCCO.{0,v,v,w} S)
variable (K E F : ExactEq S H cco ()) (hKE : K ≤ E) (hKF : K ≤ F) (hEF : E ≤ F)
local instance nestedActionsInvariantK : Invariant G K.val := exactInvariant S H cco K
local instance nestedActionsInvariantE : Invariant G E.val := exactInvariant S H cco E
local instance nestedActionsInvariantF : Invariant G F.val := exactInvariant S H cco F
local instance nestedActionsInvariantNE : Invariant G (nestedExact S H cco K E hKE).val :=
  exactInvariant (quotientSource S H cco K) (quotientSource_homogeneous S H cco K)
    (quotientSource_cco S H cco K) (nestedExact S H cco K E hKE)
local instance nestedActionsInvariantNF : Invariant G (nestedExact S H cco K F hKF).val :=
  exactInvariant (quotientSource S H cco K) (quotientSource_homogeneous S H cco K)
    (quotientSource_cco S H cco K) (nestedExact S H cco K F hKF)

theorem owner_maps_comp (q : Quotient K.val) :
    Abstract.quotientMap hEF (Abstract.quotientMap hKE q) = Abstract.quotientMap hKF q := by
  induction q using Quotient.inductionOn with | _ x => rfl

theorem imageOver (B : Set (Quotient K.val)) (x : nestedImage S H cco K E hKE B) :
    Abstract.quotientMap hEF x.val ∈ nestedImage S H cco K F hKF B := by
  obtain ⟨q, hq, heq⟩ := x.property
  refine ⟨q, hq, ?_⟩
  rw [← owner_maps_comp S H cco K E F hKE hKF hEF q]
  exact congrArg (Abstract.quotientMap hEF) heq

theorem imageOnto (B : Set (Quotient K.val)) :
    Function.Surjective (ownerProjection (Abstract.quotientMap hEF)
      (nestedImage S H cco K E hKE B) (nestedImage S H cco K F hKF B)
      (imageOver S H cco K E F hKE hKF hEF B)) := by
  intro y
  obtain ⟨q, hq, heq⟩ := y.property
  refine ⟨⟨Abstract.quotientMap hKE q, q, hq, rfl⟩, Subtype.ext ?_⟩
  exact (owner_maps_comp S H cco K E F hKE hKF hEF q).trans heq

def imageQuotient (B : Set (Quotient K.val)) :=
  inducedQuotient (G := G) (Abstract.quotientMap hEF) (quotientMap_equivariant hEF)
    (nestedImage S H cco K E hKE B) (nestedImage S H cco K F hKF B)
    (imageOver S H cco K E F hKE hKF hEF B) (imageOnto S H cco K E F hKE hKF hEF B)

theorem nested_projection_commute (q : Quotient (nestedExact S H cco K E hKE).val) :
    nestedQuotientEquiv hKF
      (Abstract.quotientMap (nestedExact_mono S H cco K E hKE F hKF hEF) q) =
      Abstract.quotientMap hEF (nestedQuotientEquiv hKE q) := by
  induction q using Quotient.inductionOn with | _ q =>
    exact (owner_maps_comp S H cco K E F hKE hKF hEF q).symm

theorem image_projection_commute (B : Set (Quotient K.val))
    (x : ((Quotient.mk'' : Quotient K.val → Quotient (nestedExact S H cco K E hKE).val) '' B)) :
    nestedImageEquiv S H cco K F hKF B
      ((exactImageQuotient (G := G) B (nestedExact S H cco K E hKE).val
        (nestedExact S H cco K F hKF).val
        (nestedExact_mono S H cco K E hKE F hKF hEF)).projection x) =
      (imageQuotient S H cco K E F hKE hKF hEF B).projection
        (nestedImageEquiv S H cco K E hKE B x) :=
  Subtype.ext (nested_projection_commute S H cco K E F hKE hKF hEF x.val)

section MasterActions
variable {T : Set (Quotient K.val)}
variable (B : ActualMaster.{v,v,t,v} (quotientSource S H cco K)
  (quotientSource_homogeneous S H cco K) (quotientSource_cco S H cco K) T)

/-- Onto restriction and fibre-transitive kernel for the literal ORIGINAL
coarse quotient images of one lower-rank master. -/
theorem master_image_m3 :
    Function.Surjective (imageQuotient S H cco K E F hKE hKF hEF B.carrier).action ∧
      GroupActions.FibreTransitive
        (imageQuotient S H cco K E F hKE hKF hEF B.carrier).action
        (imageQuotient S H cco K E F hKE hKF hEF B.carrier).projection := by
  let QE := nestedExact S H cco K E hKE
  let QF := nestedExact S H cco K F hKF
  let hQ := nestedExact_mono S H cco K E hKE F hKF hEF
  let Q := exactImageQuotient (G := G) B.carrier QE.val QF.val hQ
  apply actual_onto_kernel_of_commuting
    (imageQuotient S H cco K E F hKE hKF hEF B.carrier)
    (reverseAction (nestedImageAction S H cco K E hKE B.carrier))
    (reverseAction (nestedImageAction S H cco K F hKF B.carrier))
    Q.action Q.projection (fun g x => (Q.action_projection g x).symm) ?_
    (B.m3 QE QF hQ)
  intro x
  have h := image_projection_commute S H cco K E F hKE hKF hEF B.carrier
    ((nestedImageEquiv S H cco K E hKE B.carrier).symm x)
  rw [Equiv.apply_symm_apply] at h
  change (nestedImageEquiv S H cco K F hKF B.carrier).symm
      ((imageQuotient S H cco K E F hKE hKF hEF B.carrier).projection x) =
    Q.projection ((nestedImageEquiv S H cco K E hKE B.carrier).symm x)
  rw [← h, Equiv.symm_apply_apply]

end MasterActions
end
end CCO.RankInduction.Factors
