import CCO.TypedOrbitFrames.OldPartialPullback
import Lean.Elab.Tactic.Omega

/-!
# B053 C04: literal cyclic successors of both real chord arcs

A normalized old specified chord 0--k splits an n-cycle into
two shorter actual simple cycles. The internal directed edges
on each arc are exactly the old original cycle sides; the final
directed edges are precisely the OLD specified chord in opposite
orientations.

These are finite ordinal equalities on the actual Fin vertex
indices, not abstract assumptions that coloured homomorphic
images glue. They supply the concrete source indexing needed
to construct genuine typed shorter SimpleCycle diagrams by
pullback from the same old original PartialDiagram.
-/

namespace CCO.TypedOrbitFrames

/-- A consecutive internal LEFT subcycle edge is EXACTLY the
corresponding genuine old original directed cyclic edge.
The original closing chord is excluded here (p.val<k). -/
theorem original_chord_left_internal_next
    {n k : Nat} (cut : OriginalChordCut n k)
    (p : Fin (k + 1)) (hp : p.val < k) :
    originalChordLeftIndex cut
        (CCO.cyclicNext (by omega : 0 < k + 1) p) =
      CCO.cyclicNext
        (by have := cut.right_nontrivial; omega : 0 < n)
        (originalChordLeftIndex cut p) := by
  apply Fin.ext
  have hsmall : p.val + 1 < k + 1 := by omega
  have hbig : p.val + 1 < n := by
    have hc := cut.right_nontrivial
    omega
  change (p.val + 1) % (k + 1) =
    (p.val + 1) % n
  rw [Nat.mod_eq_of_lt hsmall, Nat.mod_eq_of_lt hbig]

/-- The last LEFT subcycle vertex is the original k position
and its short-cycle successor is the old original ZERO
position: this edge is the specified chord k→0, not a side
of the old original n-cycle. -/
theorem original_chord_left_closing_next
    {n k : Nat} (cut : OriginalChordCut n k) :
    originalChordLeftIndex cut
        (CCO.cyclicNext (by omega : 0 < k + 1)
          (⟨k, by omega⟩ : Fin (k + 1))) =
      (⟨0, by have := cut.right_nontrivial; omega⟩ : Fin n) := by
  apply Fin.ext
  simp [CCO.cyclicNext, originalChordLeftIndex]

/-- Each internal RIGHT subcycle edge is literally one
original directed side, including original wrap n-1→0.
The final short cycle edge from original 0 back to k
is the converse original chord, handled separately. -/
theorem original_chord_right_internal_next
    {n k : Nat} (cut : OriginalChordCut n k)
    (p : Fin (n - k + 1))
    (hp : p.val < n - k) :
    originalChordRightIndex cut
        (CCO.cyclicNext
          (by have := cut.right_nontrivial; omega : 0 < n - k + 1) p) =
      CCO.cyclicNext
        (by have := cut.right_nontrivial; omega : 0 < n)
        (originalChordRightIndex cut p) := by
  have hc := cut.right_nontrivial
  have hnextSmall : p.val + 1 < n - k + 1 := by omega
  have hcurr : (originalChordRightIndex cut p).val = k + p.val := by
    simp [originalChordRightIndex, hp]
  have hnext : (CCO.cyclicNext
      (by have := cut.right_nontrivial; omega : 0 < n - k + 1) p).val =
        p.val + 1 := by
    simp [CCO.cyclicNext, Nat.mod_eq_of_lt hnextSmall]
  apply Fin.ext
  by_cases hmore : p.val + 1 < n - k
  · have hnextReal :
        (originalChordRightIndex cut
          (CCO.cyclicNext
            (by have := cut.right_nontrivial; omega : 0 < n - k + 1) p)).val =
          k + p.val + 1 := by
      simp [originalChordRightIndex, hnext, hmore]
    rw [hnextReal]
    change k + p.val + 1 = (k + p.val + 1) % n
    rw [Nat.mod_eq_of_lt (by omega : k + p.val + 1 < n)]
  · have heq : k + p.val + 1 = n := by omega
    have hnextReal :
        (originalChordRightIndex cut
          (CCO.cyclicNext
            (by have := cut.right_nontrivial; omega : 0 < n - k + 1) p)).val = 0 := by
      simp [originalChordRightIndex, hnext, hmore]
    rw [hnextReal]
    change 0 = (k + p.val + 1) % n
    rw [heq]
    simp

/-- The last RIGHT subcycle vertex is the original 0,
and its short-cycle successor is the original k.
That closing edge is precisely the converse chord 0→k,
not a duplicate source side or positive identity atom. -/
theorem original_chord_right_closing_next
    {n k : Nat} (cut : OriginalChordCut n k) :
    originalChordRightIndex cut
        (CCO.cyclicNext
          (by have := cut.right_nontrivial; omega : 0 < n - k + 1)
          (⟨n - k, by omega⟩ : Fin (n - k + 1))) =
      (⟨k, by have := cut.right_nontrivial; omega⟩ : Fin n) := by
  apply Fin.ext
  have hdiff : 0 < n - k := by
    have hc := cut.right_nontrivial
    omega
  simp [CCO.cyclicNext, originalChordRightIndex, hdiff]

end CCO.TypedOrbitFrames
