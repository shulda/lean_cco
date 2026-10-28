import CCO.RawExact.CyclicIndex
import Mathlib.Data.Fin.Basic

/-!
# Deleting one position from a finite cyclic order

The literal skip embedding is the existing `Fin.succAbove`. Deletion
preserves every cyclic successor except at the predecessor of the deleted
position, where the new successor skips precisely that one position.
These are finite index facts, independent of graph or completion providers.
-/

namespace CCO.RawExact

abbrev skipIndex {m : Nat} (p : Fin (m + 1)) (r : Fin m) : Fin (m + 1) :=
  p.succAbove r

theorem skipIndex_val {m : Nat} (p : Fin (m + 1)) (r : Fin m) :
    (skipIndex p r).val = if r.val < p.val then r.val else r.val + 1 := by
  by_cases h : r.val < p.val
  · have hh : r.castSucc < p := h
    rw [skipIndex, Fin.succAbove_of_castSucc_lt p r hh, ite_eq_left h]
    rfl
  · have hh : p ≤ r.castSucc := Nat.le_of_not_gt h
    rw [skipIndex, Fin.succAbove_of_le_castSucc p r hh, ite_eq_right h]
    rfl

theorem skipIndex_injective {m : Nat} (p : Fin (m + 1)) :
    Function.Injective (skipIndex p) := Fin.succAbove_right_injective

def skipEmbedding {m : Nat} (p : Fin (m + 1)) : Fin m ↪ Fin (m + 1) :=
  ⟨skipIndex p, skipIndex_injective p⟩

theorem skipIndex_ne {m : Nat} (p : Fin (m + 1)) (r : Fin m) :
    skipIndex p r ≠ p := Fin.succAbove_ne p r

theorem exists_skipIndex_eq {m : Nat} (p q : Fin (m + 1)) (hq : q ≠ p) :
    ∃ r : Fin m, skipIndex p r = q := Fin.exists_succAbove_eq hq

theorem cyclicNext_val_formula {n : Nat} (hn : 0 < n) (p : Fin n) :
    (cyclicNext hn p).val = if p.val + 1 = n then 0 else p.val + 1 := by
  change (p.val + 1) % n = _
  by_cases h : p.val + 1 = n
  · rw [ite_eq_left h, h, Nat.mod_self]
  · have hlt : p.val + 1 < n := by have hp := p.isLt; omega
    rw [ite_eq_right h, Nat.mod_eq_of_lt hlt]

/-- The new successor either is the old successor, or skips exactly the
one deleted position. Both alternatives are literal finite-index equalities. -/
theorem skipIndex_cyclicNext {m : Nat} (hm : 0 < m)
    (p : Fin (m + 1)) (r : Fin m) :
    skipIndex p (cyclicNext hm r) = cyclicNext (Nat.succ_pos m) (skipIndex p r) ∨
      (cyclicNext (Nat.succ_pos m) (skipIndex p r) = p ∧
        skipIndex p (cyclicNext hm r) = cyclicNext (Nat.succ_pos m) p) := by
  have hr := r.isLt
  have hp := p.isLt
  by_cases hDeleted : cyclicNext (Nat.succ_pos m) (skipIndex p r) = p
  · refine Or.inr ⟨hDeleted, ?_⟩
    apply Fin.ext
    have hd := congrArg Fin.val hDeleted
    simp only [skipIndex_val, cyclicNext_val_formula] at hd ⊢
    split_ifs at hd ⊢ <;> omega
  · apply Or.inl
    apply Fin.ext
    have hd : (cyclicNext (Nat.succ_pos m) (skipIndex p r)).val ≠ p.val := by
      intro heq
      exact hDeleted (Fin.ext heq)
    simp only [skipIndex_val, cyclicNext_val_formula] at hd ⊢
    split_ifs at hd ⊢ <;> omega

theorem skipIndex_cyclicNext_of_not_deleted {m : Nat} (hm : 0 < m)
    (p : Fin (m + 1)) (r : Fin m)
    (h : cyclicNext (Nat.succ_pos m) (skipIndex p r) ≠ p) :
    skipIndex p (cyclicNext hm r) = cyclicNext (Nat.succ_pos m) (skipIndex p r) := by
  rcases skipIndex_cyclicNext hm p r with hEq | ⟨hEq, _⟩
  · exact hEq
  · exact (h hEq).elim

theorem skipIndex_cyclicNext_of_deleted {m : Nat} (hm : 0 < m)
    (p : Fin (m + 1)) (r : Fin m)
    (h : cyclicNext (Nat.succ_pos m) (skipIndex p r) = p) :
    skipIndex p (cyclicNext hm r) = cyclicNext (Nat.succ_pos m) p := by
  rcases skipIndex_cyclicNext hm p r with hEq | ⟨_, hEq⟩
  · exact ((skipIndex_ne p (cyclicNext hm r)) (hEq.trans h)).elim
  · exact hEq

/-- A nontrivial cyclic order has a predecessor of p distinct from p. -/
theorem exists_undeleted_cyclic_predecessor {m : Nat} (hm : 0 < m)
    (p : Fin (m + 1)) :
    ∃ q : Fin (m + 1), q ≠ p ∧ cyclicNext (Nat.succ_pos m) q = p := by
  have hp := p.isLt
  by_cases hp0 : p.val = 0
  · refine ⟨⟨m, Nat.lt_succ_self m⟩, ?_, ?_⟩
    · intro heq
      have hval := congrArg Fin.val heq
      simp only at hval
      omega
    · apply Fin.ext
      rw [cyclicNext_val_formula]
      change (if m + 1 = m + 1 then 0 else m + 1) = p.val
      rw [ite_eq_left rfl]
      exact hp0.symm
  · have hpos : 0 < p.val := Nat.pos_of_ne_zero hp0
    refine ⟨⟨p.val - 1, by omega⟩, ?_, ?_⟩
    · intro heq
      have hval := congrArg Fin.val heq
      simp only at hval
      omega
    · apply Fin.ext
      rw [cyclicNext_val_formula]
      change (if p.val - 1 + 1 = m + 1 then 0 else p.val - 1 + 1) = p.val
      split_ifs <;> omega

theorem exists_skipped_cyclic_predecessor {m : Nat} (hm : 0 < m)
    (p : Fin (m + 1)) :
    ∃ r : Fin m, cyclicNext (Nat.succ_pos m) (skipIndex p r) = p := by
  obtain ⟨q, hqp, hNext⟩ := exists_undeleted_cyclic_predecessor hm p
  obtain ⟨r, rfl⟩ := exists_skipIndex_eq p q hqp
  exact ⟨r, hNext⟩

theorem cyclicNext_ne_self_of_two_le {n : Nat} (hn : 0 < n) (hTwo : 2 ≤ n)
    (p : Fin n) : cyclicNext hn p ≠ p := by
  intro heq
  have hval := congrArg Fin.val heq
  rw [cyclicNext_val_formula] at hval
  have hp := p.isLt
  split_ifs at hval <;> omega

theorem exists_skipped_cyclic_successor {m : Nat} (hm : 0 < m)
    (p : Fin (m + 1)) :
    ∃ r : Fin m, skipIndex p r = cyclicNext (Nat.succ_pos m) p := by
  apply exists_skipIndex_eq
  exact cyclicNext_ne_self_of_two_le (Nat.succ_pos m) (by omega) p

end CCO.RawExact
