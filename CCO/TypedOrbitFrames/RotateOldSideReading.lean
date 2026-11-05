import CCO.TypedOrbitFrames.RotateOldSimpleCycle
import CCO.TypedOrbitFrames.CycleHomReadingConverse
import Mathlib.Tactic.Abel

/-!
# B053 C04: inverse finite rotation and exact old typed side reading

The actual finite-ordinal cyclic source rotation is a bijection,
with inverse rotation at -s. Its reindexing of a genuine old
SimpleCycle preserves the ENTIRE literal old pair-colour reading
at every side, including the original sorts, their genuine
diversity atom, and dependent proof-indexed old edge.

This is an ingredient of the source11 all-chords induction.
No completion is assumed and no source/hidden-group SAP is added.
-/

namespace CCO.TypedOrbitFrames

open CCO.ParityHasse.Sparse

universe u v w z
variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {V : Type z}

/-- Rotating an actual finite cyclic index by s and then -s
returns the LITERAL same old Fin position. -/
theorem original_cycle_rotate_inverse_index
    {n : Nat} [NeZero n] (s : ZMod n) (p : Fin n) :
    originalCycleRotateIndex s
      (originalCycleRotateIndex (-s) p) = p := by
  apply Fin.ext
  change (s +
    (((originalCycleRotateIndex (-s) p).val : Nat) : ZMod n)).val = p.val
  have hv : (((originalCycleRotateIndex (-s) p).val : Nat) : ZMod n) =
      -s + (p.val : ZMod n) := by
    change ((zmodFinCode n (-s + (p.val : ZMod n))).val : ZMod n) =
      -s + (p.val : ZMod n)
    exact ZMod.natCast_zmod_val _
  rw [hv, show s + (-s + (p.val : ZMod n)) = (p.val : ZMod n) by abel]
  exact ZMod.val_natCast_of_lt p.isLt

/-- The order of a rotation and its inverse can also be reversed;
neither changes an old cycle vertex. -/
theorem original_cycle_rotate_inverse_index_other
    {n : Nat} [NeZero n] (s : ZMod n) (p : Fin n) :
    originalCycleRotateIndex (-s)
      (originalCycleRotateIndex s p) = p := by
  simpa only [neg_neg] using
    (original_cycle_rotate_inverse_index (-s) p)

/-- Every original position occurs in the actual rotated
finite cycle; no hypothetical bijectivity of an unrelated
formal index map is used. -/
theorem original_cycle_rotate_index_surjective
    {n : Nat} [NeZero n] (s : ZMod n) :
    Function.Surjective (originalCycleRotateIndex s) := by
  intro p
  exact ⟨originalCycleRotateIndex (-s) p,
    original_cycle_rotate_inverse_index s p⟩

/-- The full typed side reading depends only on the TWO actual
formal endpoints of that side, not on its proof of inequality.
In particular a source-edge dependent certificate may be
transported by endpoint equality without rechoosing its atom. -/
theorem original_cycle_side_reading_congr
    {D : PartialDiagram S V}
    (C C' : SimpleCycle D)
    (p : Fin C.length) (q : Fin C'.length)
    (hFirst : C.vertices p = C'.vertices q)
    (hSecond :
      C.vertices (CCO.cyclicNext C.length_pos p) =
        C'.vertices (CCO.cyclicNext C'.length_pos q)) :
    originalSpecifiedCycleSideReading S C p =
      originalSpecifiedCycleSideReading S C' q := by
  dsimp only [originalSpecifiedCycleSideReading]
  rw [hFirst, hSecond]

/-- TRUE source11 old typed side colours on the rotated source
cycle are exactly the original colours at the translated index.
Nothing is required from a completed diagram or from an HN
theorem: both sides are the actual old partial diagram edges. -/
theorem original_rotated_old_cycle_side_reading
    {D : PartialDiagram S V} (C : SimpleCycle D)
    (s : ZMod C.length) (p : Fin C.length) :
    originalSpecifiedCycleSideReading S
      (originalRotateOldSimpleCycle S C s) p =
      originalSpecifiedCycleSideReading S C
        (originalCycleRotateIndex s p) := by
  letI : NeZero C.length := ⟨Nat.ne_of_gt C.length_pos⟩
  have hFirst :
      (originalRotateOldSimpleCycle S C s).vertices p =
        C.vertices (originalCycleRotateIndex s p) := rfl
  have hSecond :
      (originalRotateOldSimpleCycle S C s).vertices
          (CCO.cyclicNext
            (originalRotateOldSimpleCycle S C s).length_pos p) =
        C.vertices
          (CCO.cyclicNext C.length_pos
            (originalCycleRotateIndex s p)) := by
    exact congrArg C.vertices
      (original_cycle_rotate_next C.length_ge_three s p)
  exact original_cycle_side_reading_congr S
    (originalRotateOldSimpleCycle S C s) C
    p (originalCycleRotateIndex s p) hFirst hSecond

end CCO.TypedOrbitFrames
