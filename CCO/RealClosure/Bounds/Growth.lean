import CCO.RealClosure.Bounds.GrowthCount
import CCO.RealClosure.Bounds.SmallClosures
import CCO.RealClosure.Bounds.Singleton
import Mathlib.Data.Set.Card
import Mathlib.Logic.Equiv.Sum

/-! Actual polynomial growth of real algebraic closure and of its COMPLETE
finite packets. Bounded character supplies a finite cover by actual outside-
packet fibres, not synthetic types or a finiteness assumption on the source. -/
universe v w t
namespace CCO.RealClosure.Bounds
open ParityHasse.Original RealHull.Geometry
open scoped BigOperators
variable {M : Type v} (S : AtomicSource.{0,v,w} Unit (fun _ => M)) [DecidableEq M]
variable {G : Type t} [Group G] [MulAction G M] (H : HomogeneousSource S G)
include H

private theorem packetClosure_mono {A B : Finset M} (hAB : A ⊆ B) :
    packetClosure S H A ⊆ packetClosure S H B := by
  rintro x ⟨a,ha,hax⟩
  exact ⟨a,hAB ha,hax⟩

/-- Bounded character covers every nonpacket algebraic point by a NONEMPTY
small base. The empty base is excluded by actual infinite transitivity. -/
theorem acl_small_base_cover (cco : SemanticCCO.{0,v,0,w} S) [Infinite M] (A : Finset M) :
    Acl G A ⊆ packetClosure S H A ∪
      ⋃ B ∈ smallBases A (directionCount S), offPacketAcl S H B := by
  intro x hx
  by_cases hp : x ∈ packetClosure S H A
  · exact Or.inl hp
  · right
    obtain ⟨B,hBA,hcard,hxB⟩ := bounded_character S H cco A hx
    have hBpos : 0 < B.card := by
      by_contra hn
      have he : B = ∅ := Finset.card_eq_zero.mp (by omega)
      rw [he,acl_empty_infinite S H] at hxB
      exact hxB
    have hB : B ∈ smallBases A (directionCount S) := (mem_smallBases A _ B).mpr ⟨hBA,hBpos,hcard⟩
    exact Set.mem_iUnion.mpr ⟨B,Set.mem_iUnion.mpr ⟨hB,
      hxB,fun h => hp (packetClosure_mono S H hBA h)⟩⟩

/-- C14. First prove the actual closure FINITE from the finite cover, then
count it with the exact binomial polynomial of the pinned source. -/
theorem acl_finite_polynomial_bound (cco : SemanticCCO.{0,v,0,w} S) [Infinite M]
    (A : Finset M) :
    Finite (Acl G A) ∧ Nat.card (Acl G A) ≤ packetSize S H *
      closurePolynomial (directionCount S) (outsideAtomCount S H) A.card := by
  classical
  let I := smallBases A (directionCount S)
  let family := fun B : Finset M => offPacketAcl S H B
  have hf : ∀ B : Finset M, (family B).Finite := fun B =>
    Set.finite_coe_iff.mp (offPacketAcl_finite_bound S H cco B).1
  have hu := finite_family_card_bound I family hf
  have hwhole : (packetClosure S H A ∪ ⋃ B ∈ I, family B).Finite :=
    (packetClosure_finite S H A).union hu.1
  have hcover := acl_small_base_cover S H cco A
  refine ⟨(hwhole.subset hcover).to_subtype,?_⟩
  calc
    _ ≤ Nat.card (packetClosure S H A ∪ ⋃ B ∈ I, family B : Set M) := Set.ncard_le_ncard hcover hwhole
    _ ≤ Nat.card (packetClosure S H A) + Nat.card (⋃ B ∈ I, family B) := Set.ncard_union_le _ _
    _ ≤ packetSize S H * A.card + ∑ B ∈ I, Nat.card (family B) :=
      Nat.add_le_add (packetClosure_card_le S H A) hu.2
    _ ≤ packetSize S H * A.card + ∑ B ∈ I, packetSize S H * (outsideAtomCount S H)^B.card := by
      apply Nat.add_le_add_left
      exact Finset.sum_le_sum (fun B _ => (offPacketAcl_finite_bound S H cco B).2)
    _ = _ := by
      rw [← Finset.mul_sum]
      change packetSize S H * A.card + packetSize S H *
        (∑ B ∈ smallBases A (directionCount S), (outsideAtomCount S H)^B.card) = _
      rw [smallBases_weighted_sum]
      exact (Nat.mul_add _ _ _).symm

/-- The sharp-exponent O_M(n^r) conclusion, with an explicit coefficient
valid for ALL finite bases of size n>=1, rather than an unspecified limit. -/
theorem acl_eventual_power_bound (cco : SemanticCCO.{0,v,0,w} S) [Infinite M] :
    ∃ C : ℕ, ∀ A : Finset M, 1 ≤ A.card →
      Finite (Acl G A) ∧ Nat.card (Acl G A) ≤ C*A.card^(directionCount S) := by
  refine ⟨packetSize S H * growthCoefficient (directionCount S) (outsideAtomCount S H),?_⟩
  intro A hA
  have ha := acl_finite_polynomial_bound S H cco A
  refine ⟨ha.1,ha.2.trans ?_⟩
  exact (Nat.mul_le_mul_left _ (closurePolynomial_power_bound _ _ _
    (Nat.succ_le_iff.mpr (directionCount_pos S)) hA)).trans_eq (Nat.mul_assoc _ _ _).symm

/-- The source's empty-base point bound is literally zero. -/
theorem acl_empty_card_zero [Infinite M] : Nat.card (Acl G (∅ : Finset M)) = 0 := by
  rw [acl_empty_infinite S H]
  exact Nat.card_of_isEmpty

/-- Actual complete finite packets INSIDE the actual closure. -/
def aclPacketSetoid (A : Finset M) : Setoid (Acl G A) where
  r x y := finitePacket S H x.val y.val
  iseqv := ⟨fun x => (finitePacket S H).val.refl x.val,
    fun h => (finitePacket S H).val.symm h,
    fun h k => (finitePacket S H).val.trans h k⟩
abbrev AclPackets (A : Finset M) := Quotient (aclPacketSetoid S H A)

noncomputable def aclPacketFibreEquiv (A : Finset M) (q : AclPackets S H A) :
    {x : Acl G A // Quotient.mk (aclPacketSetoid S H A) x = q} ≃
      ClassPoint S () (finitePacket S H) q.out.val where
  toFun x := ⟨x.val.val,@Quotient.exact (Acl G A) (aclPacketSetoid S H A) q.out x.val
    ((Quotient.out_eq q).trans x.property.symm)⟩
  invFun y := ⟨⟨y.val,acl_packet_saturated S H A q.out.property y.property⟩,
    (Quotient.sound (s := aclPacketSetoid S H A) y.property).symm.trans (Quotient.out_eq q)⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- C15: actual closure is an exact finite disjoint union of c-point packets. -/
theorem acl_card_eq_packetSize_mul (cco : SemanticCCO.{0,v,0,w} S) [Infinite M]
    (A : Finset M) :
    Finite (AclPackets S H A) ∧ Nat.card (Acl G A) = packetSize S H * Nat.card (AclPackets S H A) := by
  classical
  letI := (acl_finite_polynomial_bound S H cco A).1
  letI : Finite (AclPackets S H A) := inferInstance
  letI : Fintype (AclPackets S H A) := Fintype.ofFinite _
  let f : Acl G A → AclPackets S H A := Quotient.mk _
  refine ⟨inferInstance,?_⟩
  calc
    Nat.card (Acl G A) = Nat.card (Σ q : AclPackets S H A, {x // f x = q}) :=
      (Nat.card_congr (Equiv.sigmaFiberEquiv f)).symm
    _ = ∑ q : AclPackets S H A, Nat.card {x // f x = q} := Nat.card_sigma
    _ = ∑ _q : AclPackets S H A, packetSize S H := by
      apply Finset.sum_congr rfl
      intro q _
      exact (Nat.card_congr (aclPacketFibreEquiv S H A q)).trans (packetSize_eq S H q.out.val).symm
    _ = _ := by simp only [Finset.sum_const,Finset.card_univ,← Nat.card_eq_fintype_card,nsmul_eq_mul]; exact Nat.mul_comm _ _

/-- The number of COMPLETE packets has the source polynomial without c. -/
theorem acl_packet_count_bound (cco : SemanticCCO.{0,v,0,w} S) [Infinite M]
    (A : Finset M) :
    Finite (AclPackets S H A) ∧ Nat.card (AclPackets S H A) ≤
      closurePolynomial (directionCount S) (outsideAtomCount S H) A.card := by
  have hcard := acl_card_eq_packetSize_mul S H cco A
  refine ⟨hcard.1,?_⟩
  have hbound := (acl_finite_polynomial_bound S H cco A).2
  rw [hcard.2] at hbound
  exact Nat.le_of_mul_le_mul_left hbound (packetSize_pos S H)
end CCO.RealClosure.Bounds
