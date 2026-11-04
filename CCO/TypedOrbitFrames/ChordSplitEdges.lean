import CCO.TypedOrbitFrames.ChordSplitGluing

/-!
# B053 C04: every actual original cycle SIDE survives a proper chord split

For a genuine chord 0--k of an n-cycle, both arcs contain their
original consecutive edges, without introducing edges between
nonconsecutive clone positions. The ONLY new edges in the two
shorter cycles are the two orientations of the specified chord.

Together with ChordSplitGluing, this shows that combining two
valid shorter old cycle homomorphisms using original OLD image SAP
preserves each old cycle side. The further arbitrary-rotation and
well-founded induction from an arbitrary-position chord, and the
exact typed restriction to the two shorter PartialDiagrams, remain
explicit source11 C04 obligations.
-/

namespace CCO.TypedOrbitFrames

/-- Every directed SIDE of the original specified n-cycle is one
literal directed CONSECUTIVE side of one of the two shorter arcs.
It does NOT rely on the extra chord as an old positive identity. -/
theorem original_chord_every_old_cycle_side_in_an_arc
    {n k : Nat} (cut : OriginalChordCut n k)
    (i : Fin n) :
    (∃ a b : Fin (k + 1),
      a.val + 1 = b.val ∧
      originalChordLeftIndex cut a = i ∧
      originalChordLeftIndex cut b =
        CCO.cyclicNext (by omega : 0 < n) i) ∨
    (∃ a b : Fin (n - k + 1),
      a.val + 1 = b.val ∧
      originalChordRightIndex cut a = i ∧
      originalChordRightIndex cut b =
        CCO.cyclicNext (by omega : 0 < n) i) := by
  by_cases hi : i.val < k
  · left
    let a : Fin (k + 1) := ⟨i.val, by omega⟩
    let b : Fin (k + 1) := ⟨i.val + 1, by omega⟩
    refine ⟨a,b,?_ ,?_,?_⟩
    · rfl
    · apply Fin.ext
      rfl
    · apply Fin.ext
      have hlt : i.val + 1 < n := by omega
      simp [originalChordLeftIndex, b, CCO.cyclicNext,
        Nat.mod_eq_of_lt hlt]
  · by_cases hlast : i.val + 1 < n
    · right
      let a : Fin (n - k + 1) := ⟨i.val - k, by omega⟩
      let b : Fin (n - k + 1) := ⟨i.val + 1 - k, by omega⟩
      have ha : a.val < n - k := by
        dsimp [a]
        omega
      have hb : b.val < n - k := by
        dsimp [b]
        omega
      refine ⟨a,b,?_,?_,?_⟩
      · dsimp [a,b]
        omega
      · apply Fin.ext
        simp [originalChordRightIndex, ha, a]
        omega
      · apply Fin.ext
        simp [originalChordRightIndex, hb, b,
          CCO.cyclicNext, Nat.mod_eq_of_lt hlast]
        omega
    · right
      have heq : i.val + 1 = n := by omega
      let a : Fin (n - k + 1) := ⟨i.val - k, by omega⟩
      let b : Fin (n - k + 1) := ⟨n - k, by omega⟩
      have ha : a.val < n - k := by
        dsimp [a]
        omega
      refine ⟨a,b,?_,?_,?_⟩
      · dsimp [a,b]
        omega
      · apply Fin.ext
        simp [originalChordRightIndex, ha, a]
        omega
      · apply Fin.ext
        have hmod : (i.val + 1) % n = 0 := by
          rw [heq]
          simp
        simp [originalChordRightIndex, b, CCO.cyclicNext, hmod]

end CCO.TypedOrbitFrames
