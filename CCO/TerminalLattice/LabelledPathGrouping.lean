import Mathlib.Data.List.Count
import Mathlib.Data.List.Perm.Basic

/-!
# B050 C29: extract actual repeated graph-edge labels from an ordered path

This is a finite-list combinatorial bridge between the sharp original
girth/count lemma and literal STRONG path-menu reordering.  No fake
zero-length product or equality colour is introduced.
-/

namespace CCO.TerminalLattice

private theorem perm_front_across_replicate {α : Type*}
    (a b : α) (n : Nat) (tail : List α) :
    (a :: List.replicate n b ++ tail).Perm
      (List.replicate n b ++ a :: tail) := by
  induction n with
  | zero => simp
  | succ n ih =>
      simpa only [List.replicate_succ, List.cons_append] using
        ((List.Perm.swap a b (List.replicate n b ++ tail)).symm.trans
          (List.Perm.cons b ih))

/-- A list of genuine finite labels permutes to all occurrences of a
chosen label, followed by exactly the remaining labels.  In
particular, the grouped factors have their original multiplicities. -/
theorem label_list_perm_count {r : Nat}
    (target : Fin r) (xs : List (Fin r)) :
    xs.Perm
      (List.replicate (xs.count target) target ++
        xs.filter (fun j => j != target)) := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
      by_cases h : a = target
      · subst a
        simpa [List.replicate_succ] using (List.Perm.cons target ih)
      · have hCons := List.Perm.cons a ih
        have hMove :=
          perm_front_across_replicate a target (xs.count target)
            (xs.filter (fun j => j != target))
        have hPerm := hCons.trans hMove
        simpa [h] using hPerm

/-- Extract any requested number of actual copies of one label from
an arbitrary ordered positive path, retaining a permutation of ALL
the other edge occurrences. -/
theorem label_list_perm_replicate {r : Nat}
    (target : Fin r) (xs : List (Fin r)) (n : Nat)
    (hn : n ≤ xs.count target) :
    ∃ remaining : List (Fin r),
      xs.Perm (List.replicate n target ++ remaining) := by
  refine ⟨List.replicate (xs.count target - n) target ++
      xs.filter (fun j => j != target), ?_⟩
  have hsize : n + (xs.count target - n) =
      xs.count target := Nat.add_sub_of_le hn
  have hrep : List.replicate (xs.count target) target ++
      xs.filter (fun j => j != target) =
    List.replicate n target ++
      (List.replicate (xs.count target - n) target ++
        xs.filter (fun j => j != target)) := by
    have hrepAdd (m k : Nat) :
        List.replicate (m+k) target =
          List.replicate m target ++ List.replicate k target := by
      induction m with
      | zero => simp
      | succ m ih =>
          simpa only [Nat.succ_add, List.replicate_succ, List.cons_append] using
            congrArg (List.cons target) ih
    have hrepVal :
        List.replicate (xs.count target) target =
          List.replicate n target ++
            List.replicate (xs.count target - n) target :=
      (congrArg (fun k : Nat => List.replicate k target) hsize.symm).trans
        (hrepAdd n (xs.count target - n))
    rw [hrepVal, List.append_assoc]
  rw [← hrep]
  exact label_list_perm_count target xs

end CCO.TerminalLattice
