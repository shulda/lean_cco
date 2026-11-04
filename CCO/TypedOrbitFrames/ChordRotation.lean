import CCO.TypedOrbitFrames.ChordSplitIndices
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Abel
import Lean.Elab.Tactic.Omega

namespace CCO.TypedOrbitFrames

/-- A chord between nonconsecutive positions of a simple cyclic code. -/
def OriginalZModProperChord {n : Nat} [NeZero n] (s t : ZMod n) : Prop :=
  t ≠ s ∧ t ≠ s + 1 ∧ s ≠ t + 1

/-- Rotate any proper cyclic chord to a cut 0--k with two short arcs. -/
theorem original_zmod_proper_chord_has_cut
    {n : Nat} [NeZero n] (hn : 4 ≤ n)
    (s t : ZMod n) (h : OriginalZModProperChord s t) :
    OriginalChordCut n (t - s).val := by
  obtain ⟨hne,hforward,hbackward⟩ := h
  have hlt : (t - s).val < n := ZMod.val_lt _
  have hzero : (t - s).val ≠ 0 := by
    intro hz
    exact hne (sub_eq_zero.mp ((ZMod.val_eq_zero (t - s)).mp hz))
  have hone : (t - s).val ≠ 1 := by
    intro hz
    have hd : t - s = (1 : ZMod n) :=
      (ZMod.val_eq_one (by omega : 1 < n) (t - s)).mp hz
    apply hforward
    calc
      t = (t - s) + s := by abel
      _ = 1 + s := by rw [hd]
      _ = s + 1 := by abel
  have hmin : 2 ≤ (t - s).val := by omega
  have hmax : (t - s).val + 2 ≤ n := by
    by_contra hb
    have hlast : (t - s).val = n - 1 := by omega
    have hsucc : (n - 1).succ = n := by omega
    have hneg : (-1 : ZMod n).val = n - 1 := by
      simpa only [hsucc] using (ZMod.val_neg_one (n - 1))
    have hd : t - s = -1 :=
      (ZMod.val_injective n) (hlast.trans hneg.symm)
    apply hbackward
    calc
      s = t - (t - s) := by abel
      _ = t - (-1) := by rw [hd]
      _ = t + 1 := by abel
  exact ⟨hmin,hmax⟩

open CCO.ParityHasse.Sparse

/-- Rotation of the actual original cyclic code makes s the first point. -/
theorem original_rotated_chord_zero {V : Type*} {n : Nat} [NeZero n]
    (f : CycleCode V n) (s : ZMod n) :
    (rotateCode f s) 0 = f s := by
  simp only [rotateCode_apply, add_zero]

/-- The other chord endpoint has position t-s after the rotation. -/
theorem original_rotated_chord_other {V : Type*} {n : Nat} [NeZero n]
    (f : CycleCode V n) (s t : ZMod n) :
    (rotateCode f s) (t - s) = f t := by
  rw [rotateCode_apply]
  congr 1
  abel

end CCO.TypedOrbitFrames
