import CCO.MIGeometry.ClosedPadding
import CCO.MIGeometry.RectangleSafety

/-! Actual one-sided full-support safe descent. Only the recipient owner
kernel is harmless. Opposite helper closure is controlled by nested APJ. -/
universe v w t
namespace CCO.MIGeometry
open ParityHasse.Original RealHull.Geometry RealClosure.Bounds AclOwners
open RawExact ExactCRT FinitePackets.Normalization
variable {M : Type v} (S : AtomicSource.{0,v,w} Unit (fun _ => M))
variable {G : Type t} [Group G] [MulAction G M] (H : HomogeneousSource S G)
variable (C K : ColourEq S ())

/-- The actual J/C owner kernel in the recipient's FULL invariant lattice. -/
def complementaryOwnerKernel : ColourEq (actualQuotientSource S H C) () :=
  quotientColourEq S H C (ColourEq.join S H C K) (by change C.val ≤ C.val ⊔ K.val; exact le_sup_left)

variable [Countable M] (cco : SemanticCCO.{0,v,0,w} S)
variable (BC BK : NonemptyExact S () ())
variable (hC : evaluate S BC.words = C.val.r) (hK : evaluate S BK.words = K.val.r)
include cco BC BK hC hK

/-- C23: the global universal-support palette strongly amalgamates every
finite absolutely closed recipient span. There is NO harmlessness premise
in the opposite factor and NO finite-class premise on either exact kernel. -/
theorem one_sided_full_support_safety (hCK : C.val ⊓ K.val = ⊥)
    (harmless : FullHarmless (actualQuotientSource S H C) (complementaryOwnerKernel S H C K))
    (safe : Set (Atom S)) (amalgamate : StrongClosedAmalgamation S G safe) :
    letI := originalQuotientAction S H C
    StrongClosedAmalgamation (actualQuotientSource S H C) G (fullSupportPalette S H C safe) := by
  classical
  let J := ColourEq.join S H C K
  have hCJ : C.val ≤ J.val := le_sup_left
  have hKJ : K.val ≤ J.val := le_sup_right
  have exactJ : IsExactEq S (i := ()) J.val :=
    isExactEq_sup S H (semanticCCO_change_universe S cco) ⟨BC,hC⟩ ⟨BK,hK⟩
  let BJ := exactPresentation S exactJ
  have hJ : evaluate S BJ.words = J.val.r := exactPresentation_represents S exactJ
  letI := originalQuotientAction S H C
  letI := originalQuotientAction S H K
  letI := originalQuotientAction S H J
  letI : DecidableEq (Quotient J.val) := Classical.decEq _
  let TY := actualQuotientSource S H C
  let TX := actualQuotientSource S H K
  let TO := actualQuotientSource S H J
  let HY := actualQuotient_homogeneous S H C BC hC cco
  let HX := actualQuotient_homogeneous S H K BK hK cco
  let HO := actualQuotient_homogeneous S H J BJ hJ cco
  let ownerY := Abstract.quotientMap hCJ
  let ownerX := Abstract.quotientMap hKJ
  have surjY : Function.Surjective ownerY := by
    intro q
    induction q using Quotient.inductionOn with | _ x => exact ⟨Quotient.mk'' x,rfl⟩
  have surjX : Function.Surjective ownerX := by
    intro q
    induction q using Quotient.inductionOn with | _ x => exact ⟨Quotient.mk'' x,rfl⟩
  have equivY : ∀ (g : G) y, ownerY (g • y) = g • ownerY y := by
    intro g y
    induction y using Quotient.inductionOn with | _ x => rfl
  have kernelY : ∀ y z, complementaryOwnerKernel S H C K y z ↔ ownerY y = ownerY z := by
    intro y z
    refine Quotient.inductionOn₂ y z ?_
    intro x x'
    exact (quotientColourEq_projection S H C J (show C ≤ J from hCJ) x x').trans Quotient.eq.symm
  have projectionY : ∀ A : Finset (Quotient C.val), ∀ y ∈ Acl G A,
      ownerY y ∈ Acl G (A.image ownerY) := by
    intro A y hy
    exact nested_projection_algebraic S H cco C J hCJ BC BJ hC hJ A y hy
  have projectionX : ∀ A : Finset (Quotient K.val), ∀ y ∈ Acl G A,
      ownerX y ∈ Acl G (A.image ownerX) := by
    intro A y hy
    exact nested_projection_algebraic S H cco K J hKJ BK BJ hK hJ A y hy
  intro A L R closedA closedL closedR hAL hAR
  obtain ⟨B,nonemptyB,closedB,ownersL,ownersR⟩ := closed_owner_base TO HO ownerY L R
  obtain ⟨P,closedP,spectrumP⟩ := closed_complete_owner_spectrum TX HX ownerX surjX projectionX B closedB
  obtain ⟨padding⟩ := closed_owner_padding TY HY ownerY (complementaryOwnerKernel S H C K)
    harmless surjY equivY kernelY projectionY B closedB A L R closedA hAL ownersL ownersR
  obtain ⟨g,fixes,strong,cross⟩ := padded_full_support_amalgamation S H C K cco BC BK hC hK
    hCK safe amalgamate B nonemptyB padding.base padding.left padding.right P
    padding.base_left padding.base_right padding.left_owners padding.right_owners padding.onto_base
    spectrumP padding.base_closed padding.left_closed padding.right_closed closedP
  let f := actionEmbedding TY HY padding.leftMove L
  let f' := actionEmbedding TY HY (g * padding.rightMove) R
  refine ⟨f,f',?_,?_,?_⟩
  · intro a ha
    change padding.leftMove • a = (g * padding.rightMove) • a
    rw [padding.left_fixes a ha,mul_smul,padding.right_fixes a ha,fixes a (padding.base_contains ha)]
  · intro x hx y hy
    change padding.leftMove • x = (g * padding.rightMove) • y ↔ x = y ∧ x ∈ A
    rw [mul_smul]
    constructor
    · intro he
      obtain ⟨he',hbase⟩ := (strong _ (padding.left_contains x hx) _ (padding.right_contains y hy)).mp he
      have hxA : x ∈ A := by
        by_contra hxA
        exact padding.left_off x hx hxA hbase
      have hyA : y ∈ A := by
        by_contra hyA
        exact padding.right_off y hy hyA (he' ▸ hbase)
      rw [padding.left_fixes x hxA,padding.right_fixes y hyA] at he'
      exact ⟨he',hxA⟩
    · rintro ⟨he,hxA⟩
      have hyA : y ∈ A := he ▸ hxA
      rw [padding.left_fixes x hxA,padding.right_fixes y hyA,fixes y (padding.base_contains hyA),he]
  · intro x hx hxA y hy hyA
    obtain ⟨q,hq,hcol⟩ := cross _ (padding.left_contains x hx) (padding.left_off x hx hxA)
      _ (padding.right_contains y hy) (padding.right_off y hy hyA)
    exact ⟨q,hq,by simpa only [f,f',actionEmbedding,mul_smul] using hcol⟩

end CCO.MIGeometry
