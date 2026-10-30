import CCO.RankInduction.SourceStage

/-! M1 and M3 on the original lower-master carrier itself. The self
quotient image is exactly that carrier; no double-quotient chart is
substituted for its natural full-group action. -/

universe v w t
namespace CCO.RankInduction.Factors
noncomputable section
open RawExact ExactCRT CanonicalQuotients Owners.Product Owners.Provider Owners.Master

variable {M : Type v} (S : AtomicSource.{0,v,w} Unit (fun _ => M))
variable {G : Type t} [Group G] [MulAction G M] [Countable M]
variable (H : HomogeneousSource S G) (cco : SemanticCCO.{0,v,v,w} S)
variable (K E : ExactEq S H cco ()) (hKE : K ≤ E)
local instance jointMasterActionsInvariantK : Invariant G K.val := exactInvariant S H cco K
local instance jointMasterActionsInvariantE : Invariant G E.val := exactInvariant S H cco E

omit [Countable M] in
theorem quotientMap_self (q : Quotient K.val) :
    Abstract.quotientMap (show K ≤ K from le_rfl) q = q := by
  induction q using Quotient.inductionOn with | _ x => rfl

omit [Countable M] in
theorem nestedImage_self (B : Set (Quotient K.val)) :
    nestedImage S H cco K K le_rfl B = B := by
  ext q
  constructor
  · rintro ⟨x,hx,hxq⟩
    rw [quotientMap_self S H cco K] at hxq
    exact hxq ▸ hx
  · intro hq
    exact ⟨q,hq,quotientMap_self S H cco K q⟩

variable {T : Set (Quotient K.val)}
variable (B : ActualMaster.{v,v,t,v} (quotientSource S H cco K)
  (quotientSource_homogeneous S H cco K) (quotientSource_cco S H cco K) T)

theorem master_carrier_eppa :
    EPPAFor (G := G) (ι := (Subtype.val : B.carrier → Quotient K.val))
      {x | x.val ∈ T} := by
  let e : nestedImage S H cco K K le_rfl B.carrier ≃ B.carrier :=
    Equiv.subtypeEquivRight (fun q => Iff.of_eq (congrArg (fun D : Set (Quotient K.val) => q ∈ D)
      (nestedImage_self S H cco K B.carrier)))
  apply eppaFor_equiv (Equiv.refl (Quotient K.val)) (fun _ _ => rfl) e (fun _ => rfl)
  have hp := master_image_eppa S H cco K K le_rfl B
  have ht : e ⁻¹' {x : B.carrier | x.val ∈ T} =
      {x : nestedImage S H cco K K le_rfl B.carrier |
        x.val ∈ nestedImage S H cco K K le_rfl T} := by
    ext x
    change x.val ∈ T ↔ x.val ∈ nestedImage S H cco K K le_rfl T
    rw [nestedImage_self S H cco K T]
  rw [ht]
  exact hp

theorem masterCarrierOver (x : B.carrier) :
    Abstract.quotientMap hKE x.val ∈ nestedImage S H cco K E hKE B.carrier :=
  ⟨x.val,x.property,rfl⟩

theorem masterCarrierOnto : Function.Surjective
    (ownerProjection (Abstract.quotientMap hKE) B.carrier
      (nestedImage S H cco K E hKE B.carrier) (masterCarrierOver S H cco K E hKE B)) := by
  intro y
  obtain ⟨x,hx,heq⟩ := y.property
  exact ⟨⟨x,hx⟩,Subtype.ext heq⟩

def masterCarrierQuotient :=
  inducedQuotient (G := G) (Abstract.quotientMap hKE) (quotientMap_equivariant hKE)
    B.carrier (nestedImage S H cco K E hKE B.carrier)
    (masterCarrierOver S H cco K E hKE B) (masterCarrierOnto S H cco K E hKE B)

theorem master_carrier_m3 :
    Function.Surjective (masterCarrierQuotient S H cco K E hKE B).action ∧
      GroupActions.FibreTransitive (masterCarrierQuotient S H cco K E hKE B).action
        (masterCarrierQuotient S H cco K E hKE B).projection := by
  let e : nestedImage S H cco K K le_rfl B.carrier ≃ B.carrier :=
    Equiv.subtypeEquivRight (fun q => Iff.of_eq (congrArg (fun D : Set (Quotient K.val) => q ∈ D)
      (nestedImage_self S H cco K B.carrier)))
  let Q := imageQuotient S H cco K K E le_rfl hKE hKE B.carrier
  apply actual_onto_kernel_of_commuting (masterCarrierQuotient S H cco K E hKE B)
    (fullActionEquivalenceOf (Equiv.refl (Quotient K.val)) (fun _ _ => rfl) e.symm (fun _ => rfl))
    (ActionEquivalence.refl _ _) Q.action Q.projection
    (fun g x => (Q.action_projection g x).symm) ?_
    (master_image_m3 S H cco K K E le_rfl hKE hKE B)
  intro x
  apply Subtype.ext
  rfl

end
end CCO.RankInduction.Factors
