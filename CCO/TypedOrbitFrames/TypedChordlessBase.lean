import CCO.TypedOrbitFrames.ChordGlueFromActualShortCycles
import CCO.TypedOrbitFrames.TypedSpecifiedGraph
import CCO.ParityHasse.Sparse.CycleGraph

/-!
# B053 T01/C01--C04: true old typed source chordless base reduction

The original source11 classifies chordless CCO.SimpleCycle objects
in a partial OLD atomic diagram whose REAL base is complete and
whose spokes to EVERY clone are specified. We now connect
the graph-theoretic distance-two chord obstruction with the
universal typed source-predicate OriginalNoSpecifiedProperChord.

A two-step edge is always a genuine proper nonconsecutive
cyclic chord for n>=4. The source's old edge_reverse law turns
a specified graph edge into the EXACT original typed chord
certificate in the reverse orientation required by the C04
induction. Hence a genuinely source-chordless long cycle in
a complete-base diagram has only clone vertices.

With the independently proved original old age-SAP recursive
chord-gluing step, this can yield the source11 full reduction
once the allowed local triangle and clone-only chordless
cycle witnesses are supplied. No missing edge is coloured,
no hidden SAP and no whole-diagram CCO is assumed.
-/

namespace CCO.TypedOrbitFrames

open CCO.ParityHasse.Sparse

universe u v w z t
variable {ι : Type u} {X : ι → Type v}
variable {B : Type z} {Y : Type t}
variable (S : AtomicSource.{u,v,w} ι X)

/-- On any real n-cycle of length >=4, the cyclic difference
two is neither zero nor ±one, even at the wrap-around. -/
theorem original_zmod_two_step_is_proper_chord
    {n : Nat} [NeZero n] (hn : 4 ≤ n)
    (s : ZMod n) :
    OriginalZModProperChord s (s+2) := by
  have h2 : (2 : ZMod n) ≠ 0 := zmod_two_ne_zero (by omega)
  have h21 : (2 : ZMod n) ≠ 1 := by
    intro h
    have hv := congrArg ZMod.val h
    have ha : (2 : ZMod n).val = 2 :=
      ZMod.val_natCast_of_lt (by omega)
    have hb : (1 : ZMod n).val = 1 :=
      ZMod.val_natCast_of_lt (by omega)
    rw [ha,hb] at hv
    omega
  have h3 : (3 : ZMod n) ≠ 0 := by
    intro h
    have hv := congrArg ZMod.val h
    have ha : (3 : ZMod n).val = 3 :=
      ZMod.val_natCast_of_lt (by omega)
    rw [ha, ZMod.val_zero] at hv
    omega
  refine ⟨?_,?_,?_⟩
  · intro h
    apply h2
    exact add_left_cancel
      (show s + (2 : ZMod n) = s + 0 by
        simpa only [add_zero] using h)
  · intro h
    exact h21 (add_left_cancel h)
  · intro h
    apply h3
    have h' : s + (3 : ZMod n) = s + 0 := by
      calc
        s + (3 : ZMod n) = (s + 2) + 1 := by abel
        _ = s := h.symm
        _ = s + 0 := by simp
    exact add_left_cancel h'

/-- True chordlessness of a typed original SimpleCycle
forces no distance-two specified old edge in its ACTUAL
original typed specified-edge graph. In particular a
specified positive edge at distance two would be an
existing diversity atom, not a graph-theoretic ghost. -/
theorem original_typed_chordless_implies_no_two_step
    (D : PartialDiagram S (B ⊕ Y))
    (C : SimpleCycle D) (h4 : 4 ≤ C.length)
    (hNo : OriginalNoSpecifiedProperChord S C) :
    letI : NeZero C.length := ⟨Nat.ne_of_gt C.length_pos⟩
    NoTwoStepChords (originalSpecifiedGraph S D)
      ((zmodFinCode C.length).trans C.vertices) := by
  letI : NeZero C.length := ⟨Nat.ne_of_gt C.length_pos⟩
  intro _ s hadj
  have hProp :
      OriginalZModProperChord s (s+2) :=
    original_zmod_two_step_is_proper_chord h4 s
  have hEdge :
      OriginalArbitrarySpecifiedChord S C s (s+2) := by
    change OriginalSpecifiedEdge S D
      (C.vertices (zmodFinCode C.length (s+2)))
      (C.vertices (zmodFinCode C.length s))
    have hadj' :
      (originalSpecifiedGraph S D).Adj
        (C.vertices (zmodFinCode C.length (s+2)))
        (C.vertices (zmodFinCode C.length s)) :=
      (originalSpecifiedGraph S D).symm hadj
    exact hadj'
  exact hNo s (s+2) hProp hEdge

/-- Every vertex of a true original typed chordless
long cycle in a complete old base/all-spokes diagram
is an actual CLONE vertex. This is the exact source11
C01/C02 classification, not an arbitrary graph proxy. -/
theorem original_typed_complete_base_chordless_only_clones
    (D : PartialDiagram S (B ⊕ Y))
    (hBase : OriginalCompleteBaseSpokes S D)
    (C : SimpleCycle D) (h4 : 4 ≤ C.length)
    (hNo : OriginalNoSpecifiedProperChord S C) :
    ∀ p : Fin C.length, ∃ y : Y, C.vertices p = Sum.inr y := by
  letI : NeZero C.length := ⟨Nat.ne_of_gt C.length_pos⟩
  let f : CycleCode (B ⊕ Y) C.length :=
    (zmodFinCode C.length).trans C.vertices
  have hNo2 : NoTwoStepChords (originalSpecifiedGraph S D) f :=
    original_typed_chordless_implies_no_two_step S D C h4 hNo
  have hClones := original_typed_complete_base_chordless_clone_only
    S h4 D hBase f hNo2
  intro p
  let s : ZMod C.length := (p.val : ZMod C.length)
  have hs : zmodFinCode C.length s = p := by
    apply Fin.ext
    exact ZMod.val_natCast_of_lt p.isLt
  have h := hClones s
  change ∃ y : Y,
      C.vertices (zmodFinCode C.length s) = Sum.inr y at h
  rwa [hs] at h

/-- The literal source11 chordless-cycle classification: either the whole
cycle lies among clones, or it is a triangle meeting the real old base.
All original sort and diversity-edge certificates stay in the same diagram. -/
theorem original_typed_complete_base_chordless_cases
    (D : PartialDiagram S (B ⊕ Y))
    (hBase : OriginalCompleteBaseSpokes S D)
    (C : SimpleCycle D)
    (hNo : OriginalNoSpecifiedProperChord S C) :
    (∀ p : Fin C.length, ∃ y : Y, C.vertices p = Sum.inr y) ∨
      (C.length = 3 ∧
        ∃ p : Fin C.length, ∃ d : B, C.vertices p = Sum.inl d) := by
  by_cases h4 : 4 ≤ C.length
  · exact Or.inl
      (original_typed_complete_base_chordless_only_clones S D hBase C h4 hNo)
  · have h3 : C.length = 3 := by have hge := C.length_ge_three; omega
    by_cases hTouches : ∃ p : Fin C.length, ∃ d : B,
        C.vertices p = Sum.inl d
    · exact Or.inr ⟨h3,hTouches⟩
    · left
      intro p
      cases hv : C.vertices p with
      | inl d => exact False.elim (hTouches ⟨p,d,hv⟩)
      | inr y => exact ⟨y,hv⟩

end CCO.TypedOrbitFrames
