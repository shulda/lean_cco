import CCO.TypedOrbitFrames.ChordRotation
import CCO.ParityHasse.Sparse.CycleGraph
import Mathlib.Tactic.Abel

/-!
# B053 C04: genuine finite-ordinal cyclic rotation for EVERY chord origin

The accepted ZMod→Fin cycle code identifies a group position with
the corresponding original Fin index. Translation by a group
position s is an ACTUAL embedding of all cyclic indices; it
commutes with genuine Fin cyclic successor. A chord s--t then
has endpoints zero and (t-s).val after this SINGLE rotation.

This is the finite-index foundation needed to rotate an arbitrary
old typed SimpleCycle without changing any of its displayed old
sorts or diversity edge colours; the latter dependent-typed
SimpleCycle construction is still a separate obligation.
-/

namespace CCO.TypedOrbitFrames
open CCO.ParityHasse.Sparse

/-- The actual Fin index corresponding to the cyclic position
s+j, preserving the ORIGINAL n-element cycle. -/
def originalCycleRotateIndex {n : Nat} [NeZero n]
    (s : ZMod n) : Fin n ↪ Fin n where
  toFun p := zmodFinCode n (s + (p.val : ZMod n))
  inj' := by
    intro p q heq
    have hz : s + (p.val : ZMod n) = s + (q.val : ZMod n) :=
      (zmodFinCode n).injective heq
    have hv := congrArg ZMod.val (add_left_cancel hz)
    apply Fin.ext
    simpa only [ZMod.val_natCast_of_lt p.isLt,
      ZMod.val_natCast_of_lt q.isLt] using hv

/-- Definitionally the actual cyclic translation is the pinned
ZMod-to-Fin injection applied to the translated group position. -/
@[simp] theorem originalCycleRotateIndex_apply {n : Nat} [NeZero n]
    (s : ZMod n) (p : Fin n) :
    originalCycleRotateIndex s p =
      zmodFinCode n (s + (p.val : ZMod n)) := rfl

/-- Every old Fin position is recovered from its genuine
finite cyclic coordinate; no modulo-index selection is guessed. -/
theorem original_zmod_fin_back {n : Nat} [NeZero n]
    (p : Fin n) :
    zmodFinCode n (p.val : ZMod n) = p := by
  apply Fin.ext
  exact ZMod.val_natCast_of_lt p.isLt

/-- The old source origin s becomes position zero after rotation. -/
theorem original_cycle_rotate_zero {n : Nat} [NeZero n]
    (hn : 0 < n) (s : ZMod n) :
    originalCycleRotateIndex s (⟨0, hn⟩ : Fin n) =
      zmodFinCode n s := by
  rw [originalCycleRotateIndex_apply]
  simp

/-- After rotating by s, the old point at t is at the
new exact position k=(t-s).val, with no wrap ambiguity. -/
theorem original_cycle_rotate_chord_other {n : Nat} [NeZero n]
    (s t : ZMod n) :
    originalCycleRotateIndex s
      (⟨(t-s).val, ZMod.val_lt _⟩ : Fin n) =
      zmodFinCode n t := by
  apply Fin.ext
  change (s + ((t-s).val : ZMod n)).val = t.val
  rw [ZMod.natCast_zmod_val]
  congr 1
  abel

/-- A SINGLE rotation commutes with every original cyclic SIDE.
Thus original source edge colours can be carried through the
reindexing unchanged; no fresh graph edges are inserted. -/
theorem original_cycle_rotate_next {n : Nat} [NeZero n]
    (hn : 3 ≤ n) (s : ZMod n) (p : Fin n) :
    originalCycleRotateIndex s
        (CCO.cyclicNext (by omega : 0 < n) p) =
      CCO.cyclicNext (by omega : 0 < n)
        (originalCycleRotateIndex s p) := by
  have hnext : ((CCO.cyclicNext (by omega : 0 < n) p).val : ZMod n) =
      (p.val : ZMod n) + 1 := by
    apply (zmodFinCode n).injective
    calc
      zmodFinCode n
          ((CCO.cyclicNext (by omega : 0 < n) p).val : ZMod n) =
          CCO.cyclicNext (by omega : 0 < n) p :=
        original_zmod_fin_back _
      _ = zmodFinCode n ((p.val : ZMod n) + 1) := by
        rw [zmodFinCode_add_one hn]
        rw [original_zmod_fin_back]
  change zmodFinCode n
      (s + ((CCO.cyclicNext (by omega : 0 < n) p).val : ZMod n)) =
    CCO.cyclicNext (by omega : 0 < n)
      (zmodFinCode n (s + (p.val : ZMod n)))
  rw [hnext]
  rw [show s + ((p.val : ZMod n) + 1) =
      (s + (p.val : ZMod n)) + 1 by abel]
  exact zmodFinCode_add_one hn _

end CCO.TypedOrbitFrames
