import CCO.RankInduction.NestedActions
import CCO.RankInduction.OrbitalTransfer
import CCO.RankInduction.PacketTransfer

/-! The literal finite original owner images inherit M1, full-packet M2
and actual full-group orbit coverage from one fixed lower-rank master.
No faithfulness, splitting or selected-representative assertion is used. -/

universe v w t
namespace CCO.RankInduction.Factors
noncomputable section
open RawExact ExactCRT CanonicalQuotients Owners.Product Owners.Provider Owners.Master

variable {M : Type v} (S : AtomicSource.{0,v,w} Unit (fun _ => M))
variable {G : Type t} [Group G] [MulAction G M] [Countable M]
variable (H : HomogeneousSource S G) (cco : SemanticCCO.{0,v,v,w} S)
variable (K E : ExactEq S H cco ()) (hKE : K ≤ E)
local instance nestedDecorationsInvariantK : Invariant G K.val := exactInvariant S H cco K
local instance nestedDecorationsInvariantE : Invariant G E.val := exactInvariant S H cco E
local instance nestedDecorationsInvariantNE : Invariant G (nestedExact S H cco K E hKE).val :=
  exactInvariant (quotientSource S H cco K) (quotientSource_homogeneous S H cco K)
    (quotientSource_cco S H cco K) (nestedExact S H cco K E hKE)

theorem nestedImage_eq_image (B : Set (Quotient K.val)) :
    nestedImage S H cco K E hKE B = (nestedQuotientEquiv hKE) ''
      ((Quotient.mk'' : Quotient K.val → Quotient (nestedExact S H cco K E hKE).val) '' B) := by
  ext y
  constructor
  · rintro ⟨q, hq, rfl⟩
    exact ⟨Quotient.mk'' q, ⟨q, hq, rfl⟩, rfl⟩
  · rintro ⟨q, ⟨a, ha, rfl⟩, rfl⟩
    exact ⟨a, ha, rfl⟩

variable {T : Set (Quotient K.val)}
variable (B : ActualMaster.{v,v,t,v} (quotientSource S H cco K)
  (quotientSource_homogeneous S H cco K) (quotientSource_cco S H cco K) T)

/-- M1 is retained for every original input point in the ENTIRE image. -/
theorem master_image_eppa :
    EPPAFor (G := G)
      (ι := (Subtype.val : nestedImage S H cco K E hKE B.carrier → Quotient E.val))
      {x | x.val ∈ nestedImage S H cco K E hKE T} := by
  let A := nestedExact S H cco K E hKE
  let e := nestedQuotientEquiv hKE
  let eB := nestedImageEquiv S H cco K E hKE B.carrier
  apply eppaFor_equiv e (nested_equivariant S H cco K E hKE) eB (fun _ => rfl)
  have preimage : eB ⁻¹' {x | x.val ∈ nestedImage S H cco K E hKE T} =
      {x | x.val ∈ (Quotient.mk'' : Quotient K.val → Quotient A.val) '' T} := by
    ext x
    constructor
    · rintro ⟨q, hq, heq⟩
      refine ⟨q, hq, e.injective ?_⟩
      exact heq
    · rintro ⟨q, hq, heq⟩
      exact ⟨q, hq, congrArg e heq⟩
  rw [preimage]
  exact B.eppa A

/-- M2 names the ACTUAL original coarse source packet after transport. -/
theorem master_image_closed :
    FullPacketClosed (quotientSource S H cco E) (quotientSource_homogeneous S H cco E)
      (nestedImage S H cco K E hKE B.carrier) := by
  let A := nestedExact S H cco K E hKE
  let Q := quotientSource S H cco K
  let HQ := quotientSource_homogeneous S H cco K
  let CQ := quotientSource_cco S H cco K
  have result := packet_closed_image (quotientSource Q HQ CQ A)
    (quotientSource_homogeneous Q HQ CQ A)
    (quotientSource S H cco E) (quotientSource_homogeneous S H cco E)
    (nestedQuotientEquiv hKE) (nested_equivariant S H cco K E hKE)
    ((Quotient.mk'' : Quotient K.val → Quotient A.val) '' B.carrier) (B.closed A)
  rw [← nestedImage_eq_image S H cco K E hKE B.carrier] at result
  exact result

/-- M3 to the one-point Top owner makes the FULL finite owner group
transitive. The displayed actual owner carrier may be a singleton too. -/
theorem master_image_transitive (x y : nestedImage S H cco K E hKE B.carrier) :
    ∃ g : OrbitalAut G (Quotient E.val)
      (Subtype.val : nestedImage S H cco K E hKE B.carrier → Quotient E.val), g.val x = y := by
  let F : ExactEq S H cco () := ⊤
  letI : Subsingleton (Quotient F.val) := Quotient.subsingleton_iff.mpr rfl
  let Q := imageQuotient S H cco K E F hKE le_top le_top B.carrier
  have m3 := master_image_m3 S H cco K E F hKE le_top le_top B
  have same : Q.projection x = Q.projection y := Subsingleton.elim _ _
  obtain ⟨g, _, move⟩ := m3.2 x y same
  exact ⟨g, move⟩

end
end CCO.RankInduction.Factors
