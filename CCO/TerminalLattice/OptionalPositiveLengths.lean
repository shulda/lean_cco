import CCO.TerminalLattice.OptionalPositiveNetwork

/-!
# B050 C27: exact positive-word lengths for the actual B002 private expansion

Every genuine old positive typed word contributes at least one actual
diversity edge to its RAW encoding. Missing marked pairs contribute NO
word occurrences, rather than a zero-length equality path.

This discharges the accepted B002 cycle/readout provider's
`hPositive : ∀ o, 0 < diversityLength ...` for the entire
one-word-or-absent private expansion, including all original
intermediate named sorts. No source CCO or new axiom is used.
-/

universe u v w t

namespace CCO.TerminalLattice

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {G : Type t} [Group G] [∀ i : ι, MulAction G (X i)]

/-- A genuinely positive original typed word has at least one
RAW diversity edge after deleting logical identity letters. -/
theorem original_positive_toRawWord_length_pos {i j : ι}
    (word : PositiveWord S i j) :
    0 < CCO.RawExact.diversityLength S
      (PositiveWord.toRawWord S word) := by
  induction word with
  | single a =>
      simp [PositiveWord.toRawWord, CCO.RawExact.diversityLength]
  | cons a tail ih =>
      change 0 < CCO.RawExact.diversityLength S
        (PositiveWord.toRawWord S tail) + 1
      omega

/-- Every ACTUAL private-word occurrence in the finite original
one-word-per-pair diagram has positive diversity length. Absent
marked edges have no occurrence, so not even a synthetic zero-length
equality constraint can arise.

This closes the exact hPositive interface of the B002 marked-cycle
realization and entire-diagram word-readout theorems. -/
theorem oldOptionalPositivePresentations_all_occurrences_positive
    {i : ι} {n : Nat}
    (words : CCO.RawExact.QuotientExpansion.Edge n →
      Option (PositiveWord S i i)) :
    ∀ o : CCO.RawExact.QuotientExpansion.Occurrence S
      (fun _ : Fin n => i) (oldOptionalPositivePresentations S words),
      0 < CCO.RawExact.diversityLength S
        (CCO.RawExact.QuotientExpansion.word S
          (fun _ : Fin n => i)
          (oldOptionalPositivePresentations S words) o) := by
  intro o
  rcases o with ⟨e, slot⟩
  let P := oldOptionalPositivePresentations S words
  have hMem : (P e).get slot ∈ P e :=
    List.get_mem (P e) slot
  cases h : words e with
  | none =>
      have hZero : (P e).length = 0 := by
        simp [P, oldOptionalPositivePresentations, h]
      have hBound : slot.val < (P e).length := by
        simpa only [P] using slot.isLt
      rw [hZero] at hBound
      exact False.elim (Nat.not_lt_zero slot.val hBound)
  | some w =>
      have hEq : (P e).get slot = PositiveWord.toRawWord S w := by
        simpa [P, oldOptionalPositivePresentations, h] using hMem
      change 0 < CCO.RawExact.diversityLength S ((P e).get slot)
      rw [hEq]
      exact original_positive_toRawWord_length_pos S w

end CCO.TerminalLattice
