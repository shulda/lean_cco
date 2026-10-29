import CCO.OwnerTransversal.PacketCharts
import Mathlib.Data.Set.Card

universe u v w
namespace CCO.HKNReservoir
noncomputable section
open OwnerTransversal
variable {K : Type u} [Group K] {X : Type v} [MulAction K X] {I : Type w}
variable (D : PacketCoordinates.RegularPackets (K := K) (P := X) (I := I))

/-- Coordinates for the FULL union, retaining every vertex in each chosen
packet and hence every recorded chord of its induced structure. -/
def fullPacketUnionEquiv (J : Finset I) : {x : X // D.packet x ∈ J} ≃ ↥J × K where
  toFun x := (⟨(D.coordinates x.val).1,(D.coordinates_fst x.val).symm ▸ x.property⟩,(D.coordinates x.val).2)
  invFun p := ⟨D.coordinates.symm (p.1.val,p.2),by
    rw [← D.coordinates_fst,Equiv.apply_symm_apply]
    exact p.1.property⟩
  left_inv x := by
    apply Subtype.ext
    exact D.coordinates.symm_apply_apply x.val
  right_inv p := by
    rcases p with ⟨i,k⟩
    dsimp only
    simp only [Equiv.apply_symm_apply]

theorem finite_fullPacketUnion [Finite K] (J : Finset I) : Finite {x : X // D.packet x ∈ J} :=
  Finite.of_equiv (↥J × K) (fullPacketUnionEquiv D J).symm

/-- C19: k packets have exactly k·|K| ACTUAL vertices; the HKN bound
therefore counts k·|K| and not merely the k selected origins. -/
theorem card_fullPacketUnion [Finite K] (J : Finset I) :
    Nat.card {x : X // D.packet x ∈ J} = J.card * Nat.card K := by
  rw [Nat.card_congr (fullPacketUnionEquiv D J),Nat.card_prod]
  simp only [Nat.card_eq_fintype_card,Fintype.card_coe]

 theorem card_fullPacketUnion_le [Finite K] (J : Finset I) (b : Nat) (hJ : J.card ≤ b) :
    Nat.card {x : X // D.packet x ∈ J} ≤ b * Nat.card K := by
  rw [card_fullPacketUnion]
  exact Nat.mul_le_mul_right _ hJ
end
end CCO.HKNReservoir
