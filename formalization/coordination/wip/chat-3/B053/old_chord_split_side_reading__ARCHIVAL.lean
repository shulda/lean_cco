import CCO.TypedOrbitFrames.ChordSplitEdges

/-!
# B053 C04: literal old typed colour readings survive a chord split

A general proper 0--k chord produces two strict shorter cycles. Each
ORIGINAL directed cyclic edge is a consecutive directed edge on one
of the two arcs (ChordSplitEdges), and actual old SAP glues the maps
of these arcs with agreement on BOTH endpoints (ChordHomGlue).

This theorem proves the missing colour-level step: if the two
shorter maps read each original side with its literal actual
typed old colour, then the glued full n-cycle map does so as well.
We do not postulate any new positive identity atom, make the
formal cycle into an induced age object, or replace the original
old SAP by hidden SAP.

The source11 C04 global induction still needs a concrete extraction
of an arbitrary nonconsecutive chord (with rotation) and actual
well-typed shorter source cycle diagrams. Those are not assumed
to follow automatically from this colour-reading lemma.
-/

namespace CCO.TypedOrbitFrames

universe u v w
variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)

/-- Once the old SAP two-arc images have been glued over both
chord endpoints, EVERY original old cycle side keeps EXACTLY the
prescribed finite typed pair colour. A local hypothesis is
required only for the consecutive sides of each shorter arc,
not arbitrary unspecified clone-clone pairs. -/
theorem original_chord_glue_preserves_all_old_cycle_sides
    {n k : Nat} (cut : OriginalChordCut n k)
    (left : Fin (k + 1) → Sigma X)
    (right : Fin (n - k + 1) → Sigma X)
    (readSide : Fin n → (Σ i : ι, Σ j : ι, Option (S.Atom i j)))
    (hK : left ⟨k, by omega⟩ = right ⟨0, by omega⟩)
    (h0 : left ⟨0, by omega⟩ = right ⟨n - k, by omega⟩)
    (hLeftSide : ∀ a b : Fin (k + 1), a.val + 1 = b.val →
      taggedColour S (left a) (left b) =
        readSide (originalChordLeftIndex cut a))
    (hRightSide : ∀ a b : Fin (n - k + 1), a.val + 1 = b.val →
      taggedColour S (right a) (right b) =
        readSide (originalChordRightIndex cut a)) :
    ∀ i : Fin n,
      taggedColour S
        (originalChordGlue cut left right i)
        (originalChordGlue cut left right
          (CCO.cyclicNext (by omega : 0 < n) i)) =
        readSide i := by
  intro i
  rcases original_chord_every_old_cycle_side_in_an_arc cut i with
    ⟨a,b,hab,ha,hb⟩ | ⟨a,b,hab,ha,hb⟩
  · have hfirst :
        originalChordGlue cut left right i = left a := by
      rw [← ha]
      exact original_chord_glue_left cut left right a
    have hsecond :
        originalChordGlue cut left right
          (CCO.cyclicNext (by omega : 0 < n) i) = left b := by
      rw [← hb]
      exact original_chord_glue_left cut left right b
    calc
      taggedColour S
          (originalChordGlue cut left right i)
          (originalChordGlue cut left right
            (CCO.cyclicNext (by omega : 0 < n) i)) =
          taggedColour S (left a) (left b) := by rw [hfirst,hsecond]
      _ = readSide (originalChordLeftIndex cut a) :=
        hLeftSide a b hab
      _ = readSide i := congrArg readSide ha
  · have hfirst :
        originalChordGlue cut left right i = right a := by
      rw [← ha]
      exact original_chord_glue_right cut left right hK h0 a
    have hsecond :
        originalChordGlue cut left right
          (CCO.cyclicNext (by omega : 0 < n) i) = right b := by
      rw [← hb]
      exact original_chord_glue_right cut left right hK h0 b
    calc
      taggedColour S
          (originalChordGlue cut left right i)
          (originalChordGlue cut left right
            (CCO.cyclicNext (by omega : 0 < n) i)) =
          taggedColour S (right a) (right b) := by rw [hfirst,hsecond]
      _ = readSide (originalChordRightIndex cut a) :=
        hRightSide a b hab
      _ = readSide i := congrArg readSide ha

end CCO.TypedOrbitFrames
