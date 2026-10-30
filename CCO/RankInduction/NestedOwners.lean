import CCO.RankInduction.FactorGeometry
import CCO.RankInduction.OrbitalEquivalence
import CCO.RankInduction.Basis
import CCO.Owners.Master.MasterConsumers
import CCO.Owners.Master.PacketCongruence
import CCO.Owners.Master.NestedQuotients

/-! Actual exact owner kernels INSIDE a strict original quotient. Their
double quotient is identified with the literal original coarse quotient,
including its entire finite projected carrier and full point action. -/

universe v w t
namespace CCO.RankInduction.Factors
noncomputable section
open RawExact ExactCRT CanonicalQuotients Owners.Product Owners.Provider Owners.Master

variable {M : Type v} (S : AtomicSource.{0,v,w} Unit (fun _ => M))
variable {G : Type t} [Group G] [MulAction G M] [Countable M]
variable (H : HomogeneousSource S G) (cco : SemanticCCO.{0,v,v,w} S)
variable (K E : ExactEq S H cco ()) (hKE : K ≤ E)
local instance nestedOwnersInvariantK : Invariant G K.val := exactInvariant S H cco K
local instance nestedOwnersInvariantE : Invariant G E.val := exactInvariant S H cco E

/-- Exactness of the nested owner comes from projected original RAW words. -/
def nestedExact : ExactEq (quotientSource S H cco K)
    (quotientSource_homogeneous S H cco K) (quotientSource_cco S H cco K) () :=
  ⟨nestedKernel hKE, ⟨relativeExact S H cco K E hKE,
    (relativeExact_kernel S H cco K E hKE).symm⟩⟩

theorem nestedExact_rel (x y : M) :
    (nestedExact S H cco K E hKE).val (Quotient.mk'' x) (Quotient.mk'' y) ↔ E.val x y := by
  change (Quotient.mk E.val x = Quotient.mk E.val y) ↔ E.val x y
  exact Quotient.eq

theorem nestedExact_mono (F : ExactEq S H cco ()) (hKF : K ≤ F) (hEF : E ≤ F) :
    nestedExact S H cco K E hKE ≤ nestedExact S H cco K F hKF := by
  intro q r
  induction q using Quotient.inductionOn with | _ x =>
    induction r using Quotient.inductionOn with | _ y =>
      exact fun h => (nestedExact_rel S H cco K F hKF x y).mpr
        (hEF ((nestedExact_rel S H cco K E hKE x y).mp h))

theorem nestedExact_self : nestedExact S H cco K K le_rfl = ⊥ := by
  apply Subtype.ext
  apply Setoid.ext
  intro q r
  induction q using Quotient.inductionOn with | _ x =>
    induction r using Quotient.inductionOn with | _ y =>
      change (Quotient.mk K.val x = Quotient.mk K.val y) ↔
        Quotient.mk K.val x = Quotient.mk K.val y
      rfl

local instance nestedOwnersNestedInvariant : Invariant G (nestedKernel hKE) := by
  refine ⟨?_⟩
  intro g q r hqr
  change Abstract.quotientMap hKE (g • q) = Abstract.quotientMap hKE (g • r)
  rw [quotientMap_equivariant, quotientMap_equivariant, hqr]

theorem nested_equivariant (g : G) (q : Quotient (nestedKernel hKE)) :
    nestedQuotientEquiv hKE (g • q) = g • nestedQuotientEquiv hKE q := by
  induction q using Quotient.inductionOn with | _ q =>
    exact quotientMap_equivariant hKE g q

def nestedImage (B : Set (Quotient K.val)) : Set (Quotient E.val) :=
  Abstract.quotientMap hKE '' B

/-- Every double-quotient image point is retained, with no representative
subset replacing the full actual finite coarse carrier. -/
def nestedImageEquiv (B : Set (Quotient K.val)) :
    ((Quotient.mk'' : Quotient K.val → Quotient (nestedKernel hKE)) '' B) ≃
      nestedImage S H cco K E hKE B where
  toFun x := ⟨nestedQuotientEquiv hKE x.val, by
    obtain ⟨q, hq, heq⟩ := x.property
    exact ⟨q, hq, congrArg (nestedQuotientEquiv hKE) heq⟩⟩
  invFun y := ⟨(nestedQuotientEquiv hKE).symm y.val, by
    obtain ⟨q, hq, heq⟩ := y.property
    refine ⟨q, hq, ?_⟩
    apply (nestedQuotientEquiv hKE).injective
    rw [Equiv.apply_symm_apply]
    exact heq⟩
  left_inv x := Subtype.ext ((nestedQuotientEquiv hKE).symm_apply_apply x.val)
  right_inv y := Subtype.ext ((nestedQuotientEquiv hKE).apply_symm_apply y.val)

@[simp] theorem nestedImageEquiv_val (B : Set (Quotient K.val))
    (x : ((Quotient.mk'' : Quotient K.val → Quotient (nestedKernel hKE)) '' B)) :
    (nestedImageEquiv S H cco K E hKE B x).val = nestedQuotientEquiv hKE x.val := rfl

def nestedImageAction (B : Set (Quotient K.val)) :
    ActionEquivalence
      (OrbitalAut G (Quotient (nestedKernel hKE))
        (Subtype.val : ((Quotient.mk'' : Quotient K.val → Quotient (nestedKernel hKE)) '' B) → _))
      (OrbitalAut G (Quotient E.val)
        (Subtype.val : nestedImage S H cco K E hKE B → _))
      ((Quotient.mk'' : Quotient K.val → Quotient (nestedKernel hKE)) '' B)
      (nestedImage S H cco K E hKE B) :=
  fullActionEquivalenceOf (nestedQuotientEquiv hKE) (nested_equivariant S H cco K E hKE)
    (nestedImageEquiv S H cco K E hKE B) (fun _ => rfl)

section MasterImages
variable {T : Set (Quotient K.val)}
variable (B : ActualMaster.{v,v,t,v} (quotientSource S H cco K)
  (quotientSource_homogeneous S H cco K) (quotientSource_cco S H cco K) T)

/-- M4 in the STRICT owner source realizes every compatible ORIGINAL
owner tuple inside the SAME finite master. Original exact CRT is used
only to prove compatibility of the double-quotient classes, not as a
substitute for this finite-master conclusion. -/
theorem master_realizes_images {I : Type v} [Fintype I]
    (E : I → ExactEq S H cco ()) (hKE : ∀ i, K ≤ E i)
    (q : ∀ i, Quotient (E i).val)
    (member : ∀ i, q i ∈ nestedImage S H cco K (E i) (hKE i) B.carrier)
    (compat : Abstract.Compatible (fun i => (E i).val) q) :
    ∃ b ∈ B.carrier, ∀ i, Abstract.quotientMap (hKE i) b = q i := by
  classical
  obtain ⟨a, ha⟩ := exactCRT_real_representative S H cco () E q compat
  let d := fun i => nestedExact S H cco K (E i) (hKE i)
  let qa : Quotient K.val := Quotient.mk'' a
  have members : ∀ i, (Quotient.mk'' qa : Quotient (d i).val) ∈
      (Quotient.mk'' : Quotient K.val → Quotient (d i).val) '' B.carrier := by
    intro i
    obtain ⟨b, hb, hbi⟩ := member i
    refine ⟨b, hb, Quotient.sound ?_⟩
    change Abstract.quotientMap (hKE i) b = Abstract.quotientMap (hKE i) qa
    exact hbi.trans (ha i).symm
  have compatibility : Abstract.Compatible (fun i => (d i).val)
      (fun i => Quotient.mk'' qa) := fun _ _ => rfl
  obtain ⟨b, hb, hbi⟩ := B.realizes d (fun _ => Quotient.mk'' qa) members compatibility
  refine ⟨b, hb, ?_⟩
  intro i
  exact (congrArg (nestedQuotientEquiv (hKE i)) (hbi i)).trans (ha i)

end MasterImages

end
end CCO.RankInduction.Factors
