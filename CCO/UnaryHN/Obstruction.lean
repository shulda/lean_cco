import CCO.UnaryHN.NativeTransferBasis
import Mathlib.Data.Int.Order.Basic
import Lean.Elab.Tactic.Omega

/-! The supplied obstruction premise is restricted to sources whose actual
irreducibles are already K-members. It is never inferred from SAP or unary
totality. Negative integer bounds are retained literally. -/

universe u v
namespace CCO.UnaryHN.Native

open StructuralRamsey
open StructuralRamsey.Structure

def RestrictedObstruction {L : Language.{u}} (K : Class.{u,v} L) (N : ℤ) : Prop :=
  ∀ {V : Type v} [Finite V] (C : Structure L V), C.SingletonValued →
    IrreduciblesIn K C → ¬ HasCompletion K C →
    ∃ (S : Finset V) (hS : C.IsClosed (↑S : Set V)),
      (S.card : ℤ) ≤ N ∧ ¬ HasCompletion K (C.induce (↑S : Set V) hS)

def obstructionCutoff (N : ℤ) : ℕ := (max 1 N).toNat

theorem obstructionCutoff_pos (N : ℤ) : 0 < obstructionCutoff N := by
  unfold obstructionCutoff
  omega

theorem card_le_obstructionCutoff {n : ℕ} {N : ℤ} (h : (n : ℤ) ≤ N) :
    n ≤ obstructionCutoff N := by
  unfold obstructionCutoff
  omega

theorem completion_of_restricted_local_tests {L : Language.{u}} {K : Class.{u,v} L}
    {N : ℤ} (hN : RestrictedObstruction K N)
    {V : Type v} [Finite V] (C : Structure L V) (hSingle : C.SingletonValued)
    (hPieces : IrreduciblesIn K C)
    (hLocal : ClosedSmallCompletable K C (obstructionCutoff N)) : HasCompletion K C := by
  by_contra hNo
  obtain ⟨S, hS, hSize, hBad⟩ := hN C hSingle hPieces hNo
  exact hBad (hLocal S (card_le_obstructionCutoff hSize) hS)

end CCO.UnaryHN.Native
