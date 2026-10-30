import CCO.RankInduction.Basis
import CCO.RealClosure.Bounds.ExactDirections

/-! Every minimal infinite direction is retained: the normalized split
is exactly one direction or at least two, with none omitted. -/

universe v w
namespace CCO.RankInduction
open RealClosure.Bounds

variable {M : Type v} (S : AtomicSource.{0,v,w} Unit (fun _ => M)) [Infinite M]

theorem direction_cases :
    (∃ D : Direction S, ∀ D' : Direction S, D' = D) ∨ 2 ≤ directionCount S := by
  classical
  by_cases many : 2 ≤ directionCount S
  · exact Or.inr many
  · have := direction_nonempty_of_infinite S
    obtain ⟨D⟩ := (inferInstance : Nonempty (Direction S))
    let _ : Fintype (Direction S) := Fintype.ofFinite _
    have bound : Fintype.card (Direction S) ≤ 1 := by
      have hb : directionCount S ≤ 1 := by omega
      simpa only [directionCount,Nat.card_eq_fintype_card] using hb
    have subsingleton := Fintype.card_le_one_iff_subsingleton.mp bound
    exact Or.inl ⟨D,fun D' => subsingleton.elim D' D⟩

end CCO.RankInduction
