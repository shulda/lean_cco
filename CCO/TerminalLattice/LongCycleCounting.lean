import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Basic

/-!
# B050 C29: the sharp labelled-cycle closing-edge count

This is the finite pigeonhole step in source v27 section 08, N06.
A simple root-skeleton graph cycle of length m strictly greater than
r*(N-1)+1 can be opened at ANY selected closing edge and STILL has
at least N other edges of one label.

The claim is stronger than selecting a different closing label when
possible, and has no assumptions about the existence of an ambient
CCO completion, SAP, exactness, labels being distinct, or an injective
graph homomorphism. The following source step must combine this count
with old same-sort STRONG commutation, literal powers and absorption.
-/

universe u

namespace CCO.TerminalLattice

open scoped BigOperators

/-- The multiplicity of one of r original graph-edge labels on a
finite set of formal edges. Only actual occurrences are counted. -/
def finiteLabelCount {α : Type u} [DecidableEq α]
    {r : Nat} (edges : Finset α) (labels : α → Fin r)
    (i : Fin r) : Nat :=
  edges.sum (fun e => if labels e = i then 1 else 0)

/-- Count each finite formal edge once, using exactly its given label.
There are no exceptional edges or fictitious labels. -/
theorem finiteLabelCount_total {α : Type u} [DecidableEq α]
    {r : Nat} (edges : Finset α) (labels : α → Fin r) :
    (∑ i : Fin r, finiteLabelCount edges labels i) = edges.card := by
  unfold finiteLabelCount
  calc
    (∑ i : Fin r, edges.sum (fun e => if labels e = i then 1 else 0)) =
        edges.sum (fun e => ∑ i : Fin r, if labels e = i then 1 else 0) := by
          rw [Finset.sum_comm]
    _ = edges.sum (fun _ => 1) := by
      apply Finset.sum_congr rfl
      intro e _
      simp
    _ = edges.card := by simp

/-- C29's finite pigeonhole bound for any given set of graph-cycle
edges. If more than r*(N-1) remain, some label occurs at least N
times, with literal finite multiplicities. -/
theorem long_cycle_has_many_labels {α : Type u} [DecidableEq α]
    {r N : Nat} (edges : Finset α) (labels : α → Fin r)
    (hLong : r * (N-1) < edges.card) :
    ∃ i : Fin r, N ≤ finiteLabelCount edges labels i := by
  classical
  by_contra hbad
  have hsmall (i : Fin r) :
      finiteLabelCount edges labels i ≤ N-1 := by
    have hnot : ¬ N ≤ finiteLabelCount edges labels i := by
      intro h
      exact hbad ⟨i, h⟩
    omega
  have hsum :
      (∑ i : Fin r, finiteLabelCount edges labels i) ≤
        ∑ _i : Fin r, (N-1) :=
    Finset.sum_le_sum (fun i _ => hsmall i)
  rw [finiteLabelCount_total] at hsum
  simp only [Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul] at hsum
  omega

/-- Exact original graph-cycle guard counting at the SOURCE threshold:
after deleting ANY specified closing edge, a label still has N
occurrences on the complementary simple path.

The source uses m > r*(N-1)+1; the proof needs no label-selection
case split, because the strict +1 leaves enough edges even if the
chosen closing edge has the most frequent label. -/
theorem long_cycle_delete_any_closing_edge
    {m r N : Nat} (labels : Fin m → Fin r)
    (hLong : r * (N-1)+1 < m)
    (closing : Fin m) :
    ∃ i : Fin r,
      N ≤ finiteLabelCount
        ((Finset.univ : Finset (Fin m)).erase closing) labels i := by
  classical
  have hcard :
      ((Finset.univ : Finset (Fin m)).erase closing).card = m-1 := by
    simp
  apply long_cycle_has_many_labels
  rw [hcard]
  omega

end CCO.TerminalLattice
