import CCO.TypedOrbitFrames.ChordSplitIndices

/-!
# B053 C04: literal source-map gluing across a proper chord

The previous module proves the two shorter finite arcs cover the
original n-cycle and overlap ONLY on the two chord endpoints.
This module proves that a pair of maps from those two ACTUAL
subcycle indices into a common target, with matching endpoints,
defines one total map on ALL original vertices. Its restrictions
are literally the supplied maps; no other source vertices need
to be identified, and the target can be the genuine original
old SAP amalgam from ChordHomGlue.

This closes the combinatorial "thread the image maps back through
the chord" operation. The further theorem that every arbitrary
cycle can first be rotated to a proper chord at 0,k, and its
recursive subcycles are valid specified typed cycles, still
requires the separate source11 C04 induction.
-/

namespace CCO.TypedOrbitFrames

universe u
variable {A : Type u} {n k : Nat}

/-- A literal total map on all n original cycle positions obtained
by taking the left map at indices 0..k and the right map at k+1..n-1.
At the right endpoint 0 and left endpoint k the two maps must
agree for this to represent their common actual old SAP target. -/
def originalChordGlue
    (cut : OriginalChordCut n k)
    (left : Fin (k + 1) → A)
    (right : Fin (n - k + 1) → A) :
    Fin n → A :=
  fun i =>
    if h : i.val ≤ k then
      left ⟨i.val, by omega⟩
    else
      right ⟨i.val - k, by omega⟩

/-- The glued map is EXACTLY the supplied left map on every
position of the first subcycle, not merely on its two endpoints. -/
theorem original_chord_glue_left
    (cut : OriginalChordCut n k)
    (left : Fin (k + 1) → A)
    (right : Fin (n - k + 1) → A)
    (a : Fin (k + 1)) :
    originalChordGlue cut left right (originalChordLeftIndex cut a) = left a := by
  have ha : a.val ≤ k := by omega
  simp [originalChordGlue, originalChordLeftIndex, ha]

/-- The source gluing agrees with the whole second subcycle:
its first k-endpoint uses the first map's last vertex and its
last 0-endpoint uses the first map's first vertex. The TWO
agreement equations are exactly those supplied by the genuine
old-image chord SAP gluing theorem. -/
theorem original_chord_glue_right
    (cut : OriginalChordCut n k)
    (left : Fin (k + 1) → A)
    (right : Fin (n - k + 1) → A)
    (hK : left ⟨k, by omega⟩ = right ⟨0, by omega⟩)
    (h0 : left ⟨0, by omega⟩ = right ⟨n - k, by omega⟩)
    (b : Fin (n - k + 1)) :
    originalChordGlue cut left right (originalChordRightIndex cut b) = right b := by
  by_cases hb : b.val < n - k
  · by_cases hz : b.val = 0
    · have hbb : b = ⟨0, by omega⟩ := Fin.ext hz
      subst b
      simpa [originalChordGlue, originalChordRightIndex,
        show 0 < n - k by omega] using hK
    · have hnot : ¬ (k + b.val ≤ k) := by omega
      simp [originalChordGlue, originalChordRightIndex, hb, hnot]
  · have hlast : b.val = n - k := by omega
    have hbb : b = ⟨n - k, by omega⟩ := Fin.ext hlast
    subst b
    simpa [originalChordGlue, originalChordRightIndex] using h0

/-- The pair of real old-image maps from a proper chord split
lifts into one total original-cycle map. Both restrictions,
not only their chord endpoints, are preserved simultaneously. -/
theorem original_chord_glue_total
    (cut : OriginalChordCut n k)
    (left : Fin (k + 1) → A)
    (right : Fin (n - k + 1) → A)
    (hK : left ⟨k, by omega⟩ = right ⟨0, by omega⟩)
    (h0 : left ⟨0, by omega⟩ = right ⟨n - k, by omega⟩) :
    ∃ whole : Fin n → A,
      (∀ a : Fin (k + 1),
        whole (originalChordLeftIndex cut a) = left a) ∧
      (∀ b : Fin (n - k + 1),
        whole (originalChordRightIndex cut b) = right b) := by
  exact ⟨originalChordGlue cut left right,
    original_chord_glue_left cut left right,
    original_chord_glue_right cut left right hK h0⟩

end CCO.TypedOrbitFrames
