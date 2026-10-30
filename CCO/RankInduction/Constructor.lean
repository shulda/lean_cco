import CCO.RankInduction.NormalizedConstruction
import CCO.RankInduction.FiniteBoundary

/-! Plain rank construction and its SEPARATE closed refinement. The
original plain theorem consumes Lower only; arbitrary supplied plain
quotient witnesses are never asserted closed. -/

universe v w t
namespace CCO.RankInduction
noncomputable section
open RawExact RealClosure.Bounds FinitePackets.Normalization

variable {M : Type v} (S : AtomicSource.{0,v,w} Unit (fun _ => M))
variable {G : Type t} [Group G] [MulAction G M] [Countable M]
variable (H : HomogeneousSource S G) (cco : SemanticCCO.{0,v,v,w} S)

theorem rank_relative_constructor (lower : Lower S G H cco) : Rooted S G := by
  classical
  rcases finite_or_infinite M with finiteM | infiniteM
  · have := finiteM
    exact ClosedRooted.rooted _ G (finite_closed_rooted S H)
  · have := infiniteM
    rcases normalized_or_greatest_finite S H cco with normalized | ⟨proper,finiteK⟩
    · exact ClosedRooted.rooted _ G (normalized_constructor S H cco normalized lower)
    · intro safe hs A0 finiteA nonemptyA
      exact finite_exact_plain S H cco (greatestFiniteExact S H cco) proper finiteK lower
        safe hs A0 finiteA nonemptyA

theorem closed_rank_constructor (lower : Lower S G H cco)
    (lowerClosed : LowerClosed S G H cco) : ClosedRooted S G := by
  classical
  rcases finite_or_infinite M with finiteM | infiniteM
  · have := finiteM
    exact finite_closed_rooted S H
  · have := infiniteM
    rcases normalized_or_greatest_finite S H cco with normalized | ⟨proper,finiteK⟩
    · exact normalized_constructor S H cco normalized lower
    · intro safe hs A0 finiteA nonemptyA
      exact finite_exact_closed S H cco (greatestFiniteExact S H cco) proper finiteK lowerClosed
        safe hs A0 finiteA nonemptyA

end
end CCO.RankInduction
