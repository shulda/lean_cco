import CCO.StrongGeometry
import CCO.SAPPoint
import CCO.SAPEdge
import Mathlib.Data.Fintype.Powerset
import Mathlib.Order.OrderIsoNat

/-! Positive STRONG loop powers. Index `n` means exponent `n+1`; no
zeroth strong menu or equality atom is introduced. -/
universe u v w
namespace CCO.Selectors
variable {ι : Type u} {X : ι → Type v} (S : AtomicSource.{u,v,w} ι X)
variable {i : ι}

def loopPower (P : S.Menu i i) : Nat → S.Menu i i
  | 0 => P
  | n+1 => S.product (loopPower P n) P

@[simp] theorem loopPower_zero (P : S.Menu i i) : loopPower S P 0 = P := rfl
@[simp] theorem loopPower_succ (P : S.Menu i i) (n : Nat) :
    loopPower S P (n+1) = S.product (loopPower S P n) P := rfl

theorem loopPower_add (edge : S.RealEdgeGluing) (P : S.Menu i i) (a b : Nat) :
    S.product (loopPower S P a) (loopPower S P b) = loopPower S P (a+b+1) := by
  induction b with
  | zero => simp
  | succ b ih =>
    rw [loopPower_succ, ← S.product_assoc_of_edge_gluing edge, ih]
    simp only [loopPower_succ]
    congr 1 <;> omega

theorem loopPower_nonempty (point : S.RealPointGluing) (P : S.Menu i i)
    (hP : P.Nonempty) (n : Nat) : (loopPower S P n).Nonempty := by
  induction n with
  | zero => exact hP
  | succ n ih => exact S.product_nonempty_of_point_gluing point ih hP

theorem loopPower_step_two (point : S.RealPointGluing) (edge : S.RealEdgeGluing)
    (P : S.Menu i i) (hP : P.Nonempty) (n : Nat) :
    loopPower S P n ⊆ loopPower S P (n+2) := by
  induction n with
  | zero => exact S.loop_powers_three_of_gluing point edge P hP
  | succ n ih => exact S.product_mono ih (fun _ h => h)

theorem loopPower_parity_monotone (point : S.RealPointGluing) (edge : S.RealEdgeGluing)
    (P : S.Menu i i) (hP : P.Nonempty) (r : Nat) :
    Monotone (fun n => loopPower S P (2*n+r)) := by
  apply monotone_nat_of_le_succ
  intro n
  simpa only [show 2*(n+1)+r = (2*n+r)+2 by omega] using
    loopPower_step_two S point edge P hP (2*n+r)

/-- Stable even and odd positive powers, including the original loop.
Only point/edge SAP geometry and the actual finite palette are used. -/
theorem loopPower_even_odd (point : S.RealPointGluing) (edge : S.RealEdgeGluing)
    (P : S.Menu i i) (hP : P.Nonempty) :
    ∃ N : Nat, let J := loopPower S P (2*N+1); let O := loopPower S P (2*N)
      J.Nonempty ∧ O.Nonempty ∧ S.product J J = J ∧
      S.product J O = O ∧ S.product O O = J ∧ P ⊆ O ∧
      (∀ n, N ≤ n → loopPower S P (2*n+1) = J) ∧
      (∀ n, N ≤ n → loopPower S P (2*n) = O) := by
  classical
  letI : Fintype (S.Atom i i) := S.finiteAtom i i
  letI : Finite (S.Menu i i) := inferInstance
  obtain ⟨e, he⟩ := WellFoundedGT.monotone_chain_condition
    (⟨fun n => loopPower S P (2*n+1), loopPower_parity_monotone S point edge P hP 1⟩ :
      Nat →o S.Menu i i)
  obtain ⟨o, ho⟩ := WellFoundedGT.monotone_chain_condition
    (⟨fun n => loopPower S P (2*n), loopPower_parity_monotone S point edge P hP 0⟩ :
      Nat →o S.Menu i i)
  let N := max e o
  have hE (n : Nat) (hn : N ≤ n) :
      loopPower S P (2*n+1) = loopPower S P (2*N+1) :=
    (he n (le_trans (le_max_left _ _) hn)).symm.trans (he N (le_max_left _ _))
  have hO (n : Nat) (hn : N ≤ n) :
      loopPower S P (2*n) = loopPower S P (2*N) :=
    (ho n (le_trans (le_max_right _ _) hn)).symm.trans (ho N (le_max_right _ _))
  refine ⟨N, loopPower_nonempty S point P hP _, loopPower_nonempty S point P hP _,
    ?_, ?_, ?_, ?_, hE, hO⟩
  · rw [loopPower_add S edge]
    rw [show (2*N+1)+(2*N+1)+1 = 2*(2*N+1)+1 by omega]
    exact hE (2*N+1) (by omega)
  · rw [loopPower_add S edge]
    rw [show (2*N+1)+(2*N)+1 = 2*(2*N+1) by omega]
    exact hO (2*N+1) (by omega)
  · rw [loopPower_add S edge]
    rw [show (2*N)+(2*N)+1 = 2*(2*N)+1 by omega]
    exact hE (2*N) (by omega)
  · exact loopPower_parity_monotone S point edge P hP 0 (Nat.zero_le N)

end CCO.Selectors
