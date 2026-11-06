import CCO.TypedOrbitFrames.RotateOldSideReading
import CCO.TypedOrbitFrames.ChordShortRight

/-!
# B053 C04: literal old atom readings on the TWO actual short source cycles

The real shorter cycles produced from an actual specified 0--k
old chord have the SAME source PartialDiagram D. Each INTERNAL
short directed side is exactly an original side, so a true old
CycleHom of either shorter cycle yields the original old tagged
atom reading there. Only the two closing sides are separately
the original specified chord and its converse.

No replacement of typed old edges by graph adjacency or
unproved whole-diagram completion is made.
-/

namespace CCO.TypedOrbitFrames

universe u v w z
variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {V : Type z}

/-- The actual LEFT short source cycle retains every original
typed atom on each internal directed side, including its
dependent old source and target sort. -/
theorem original_left_short_internal_tagged_reading
    {D : PartialDiagram S V} (C : SimpleCycle D)
    {k : Nat} (cut : OriginalChordCut C.length k)
    (hChord : OriginalNormalizedSpecifiedChord S C cut)
    (p : Fin (k + 1)) (hp : p.val < k) :
    originalSpecifiedCycleSideReading S
      (originalChordLeftShortCycle S C cut hChord) p =
      originalSpecifiedCycleSideReading S C
        (originalChordLeftIndex cut p) := by
  have hFirst :
      (originalChordLeftShortCycle S C cut hChord).vertices p =
      C.vertices (originalChordLeftIndex cut p) := rfl
  have hSecond :
      (originalChordLeftShortCycle S C cut hChord).vertices
        (CCO.cyclicNext
          (originalChordLeftShortCycle S C cut hChord).length_pos p) =
      C.vertices (CCO.cyclicNext C.length_pos
        (originalChordLeftIndex cut p)) := by
    change C.vertices
      (originalChordLeftIndex cut
        (CCO.cyclicNext (by omega : 0 < k + 1) p)) =
      C.vertices (CCO.cyclicNext C.length_pos
        (originalChordLeftIndex cut p))
    exact congrArg C.vertices
      (original_chord_left_internal_next cut p hp)
  exact original_cycle_side_reading_congr S
    (originalChordLeftShortCycle S C cut hChord) C
    p (originalChordLeftIndex cut p) hFirst hSecond

/-- The actual RIGHT short source cycle retains every original
typed atom on each internal side, including the genuine old
n-1→0 wrap. The converse old chord is the distinct closing
edge and is not included in this assertion. -/
theorem original_right_short_internal_tagged_reading
    {D : PartialDiagram S V} (C : SimpleCycle D)
    {k : Nat} (cut : OriginalChordCut C.length k)
    (hChord : OriginalNormalizedSpecifiedChord S C cut)
    (p : Fin (C.length - k + 1))
    (hp : p.val < C.length - k) :
    originalSpecifiedCycleSideReading S
      (originalChordRightShortCycle S C cut hChord) p =
      originalSpecifiedCycleSideReading S C
        (originalChordRightIndex cut p) := by
  have hFirst :
      (originalChordRightShortCycle S C cut hChord).vertices p =
      C.vertices (originalChordRightIndex cut p) := rfl
  have hSecond :
      (originalChordRightShortCycle S C cut hChord).vertices
        (CCO.cyclicNext
          (originalChordRightShortCycle S C cut hChord).length_pos p) =
      C.vertices (CCO.cyclicNext C.length_pos
        (originalChordRightIndex cut p)) := by
    change C.vertices
      (originalChordRightIndex cut
        (CCO.cyclicNext
          (by have := cut.right_nontrivial; omega :
            0 < C.length - k + 1) p)) =
      C.vertices (CCO.cyclicNext C.length_pos
        (originalChordRightIndex cut p))
    exact congrArg C.vertices
      (original_chord_right_internal_next cut p hp)
  exact original_cycle_side_reading_congr S
    (originalChordRightShortCycle S C cut hChord) C
    p (originalChordRightIndex cut p) hFirst hSecond

end CCO.TypedOrbitFrames
