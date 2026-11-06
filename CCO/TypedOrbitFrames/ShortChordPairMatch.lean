import CCO.TypedOrbitFrames.OriginalPairReadings
import CCO.TypedOrbitFrames.ShortCycleSideReading

/-!
# B053 C04: actual short old CycleHom pair matches the SAME original chord

The two real typed shorter cycles from one specified old 0--k chord
have closing edges in opposite orientations. Their actual old
homomorphism image tuples MUST read the identical full old pair
colour from k to 0; this is not the weaker assertion that
each endpoint can be aligned independently.

We prove the exact tagged pair equality via literal old
PartialDiagram.edge_reverse and transport of BOTH formal endpoints.
The source chord is a positive OLD diversity atom and makes both
image points genuinely distinct, never a fictitious identity atom.
-/

namespace CCO.TypedOrbitFrames

universe u v w z
variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {V : Type z}

/-- Full actual old tagged chord colour of the LEFT and RIGHT
shorter CycleHom tuples, in the same k-to-zero orientation.
Both tuples read actual old source edges of the SAME PartialDiagram. -/
theorem original_short_cycles_same_full_chord_reading
    {D : PartialDiagram S V} (C : SimpleCycle D)
    {k : Nat} (cut : OriginalChordCut C.length k)
    (hChord : OriginalNormalizedSpecifiedChord S C cut)
    (left : Fin (k+1) → Sigma X)
    (right : Fin (C.length-k+1) → Sigma X)
    (hLeftRead : ∀ p : Fin (k+1),
      taggedColour S (left p)
        (left (CCO.cyclicNext
          (originalChordLeftShortCycle S C cut hChord).length_pos p)) =
        originalSpecifiedCycleSideReading S
          (originalChordLeftShortCycle S C cut hChord) p)
    (hRightRead : ∀ p : Fin (C.length-k+1),
      taggedColour S (right p)
        (right (CCO.cyclicNext
          (originalChordRightShortCycle S C cut hChord).length_pos p)) =
        originalSpecifiedCycleSideReading S
          (originalChordRightShortCycle S C cut hChord) p) :
    let lK : Fin (k+1) := ⟨k, by have hc := cut.left_nontrivial; omega⟩
    let l0 : Fin (k+1) := ⟨0, by omega⟩
    let r0 : Fin (C.length-k+1) :=
      ⟨0, by have hc := cut.right_nontrivial; omega⟩
    let rLast : Fin (C.length-k+1) := ⟨C.length-k, by omega⟩
    taggedColour S (left lK) (left l0) =
      taggedColour S (right r0) (right rLast) ∧
    left lK ≠ left l0 := by
  let L : SimpleCycle D := originalChordLeftShortCycle S C cut hChord
  let R : SimpleCycle D := originalChordRightShortCycle S C cut hChord
  let lK : Fin (k+1) := ⟨k, by have := cut.left_nontrivial; omega⟩
  let l0 : Fin (k+1) := ⟨0, by omega⟩
  let r0 : Fin (C.length-k+1) :=
    ⟨0, by have := cut.right_nontrivial; omega⟩
  let rLast : Fin (C.length-k+1) :=
    ⟨C.length-k, by omega⟩
  have hLN : CCO.cyclicNext L.length_pos lK = l0 := by
    apply Fin.ext
    change (k+1) % (k+1) = 0
    simp
  have hRN : CCO.cyclicNext R.length_pos rLast = r0 := by
    apply Fin.ext
    change (C.length-k+1) % (C.length-k+1) = 0
    simp
  have hcNe :
      C.vertices (originalChordOldK cut) ≠
        C.vertices (originalChordOldZero cut) :=
    C.vertices.injective.ne (original_chord_old_K_ne_zero cut)
  have hLK : L.vertices lK =
      C.vertices (originalChordOldK cut) := by
    change C.vertices (originalChordLeftIndex cut lK) =
      C.vertices (originalChordOldK cut)
    exact congrArg C.vertices (original_chord_left_last cut)
  have hL0 : L.vertices (CCO.cyclicNext L.length_pos lK) =
      C.vertices (originalChordOldZero cut) := by
    change C.vertices (originalChordLeftIndex cut
      (CCO.cyclicNext (by omega : 0 < k+1) lK)) =
      C.vertices (originalChordOldZero cut)
    exact congrArg C.vertices (original_chord_left_closing_next cut)
  have hR0 : R.vertices rLast =
      C.vertices (originalChordOldZero cut) := by
    change C.vertices (originalChordRightIndex cut rLast) =
      C.vertices (originalChordOldZero cut)
    exact congrArg C.vertices (original_chord_right_last cut)
  have hRK : R.vertices (CCO.cyclicNext R.length_pos rLast) =
      C.vertices (originalChordOldK cut) := by
    change C.vertices (originalChordRightIndex cut
      (CCO.cyclicNext
        (by have hc := cut.right_nontrivial; omega :
          0 < C.length-k+1) rLast)) =
      C.vertices (originalChordOldK cut)
    exact congrArg C.vertices (original_chord_right_closing_next cut)
  have hSourceL :
      originalSpecifiedCycleSideReading S L lK =
        originalTypedPairReading S D hcNe := by
    change originalTypedPairReading S D (L.next_ne lK) =
      originalTypedPairReading S D hcNe
    exact original_typed_pair_reading_endpoint_congr
      S D hLK hL0 (L.next_ne lK) hcNe
  have hSourceR :
      originalSpecifiedCycleSideReading S R rLast =
        originalTypedPairReading S D hcNe.symm := by
    change originalTypedPairReading S D (R.next_ne rLast) =
      originalTypedPairReading S D hcNe.symm
    exact original_typed_pair_reading_endpoint_congr
      S D hR0 hRK (R.next_ne rLast) hcNe.symm
  have hL :
      taggedColour S (left lK) (left l0) =
        originalTypedPairReading S D hcNe := by
    calc
      taggedColour S (left lK) (left l0) =
          taggedColour S (left lK)
            (left (CCO.cyclicNext L.length_pos lK)) :=
        congrArg (fun p : Fin (k+1) => taggedColour S (left lK) (left p)) hLN.symm
      _ = originalSpecifiedCycleSideReading S L lK := hLeftRead lK
      _ = originalTypedPairReading S D hcNe := hSourceL
  have hR :
      taggedColour S (right rLast) (right r0) =
        originalTypedPairReading S D hcNe.symm := by
    calc
      taggedColour S (right rLast) (right r0) =
          taggedColour S (right rLast)
            (right (CCO.cyclicNext R.length_pos rLast)) :=
        congrArg
          (fun p : Fin (C.length-k+1) => taggedColour S (right rLast) (right p))
          hRN.symm
      _ = originalSpecifiedCycleSideReading S R rLast := hRightRead rLast
      _ = originalTypedPairReading S D hcNe.symm := hSourceR
  have hSame :
      taggedColour S (left lK) (left l0) =
        taggedColour S (right r0) (right rLast) := by
    calc
      taggedColour S (left lK) (left l0) =
          originalTypedPairReading S D hcNe := hL
      _ = originalTypedPairConverse S
          (originalTypedPairReading S D hcNe.symm) :=
        original_typed_pair_reading_converse S D hcNe
      _ = originalTypedPairConverse S
          (taggedColour S (right rLast) (right r0)) :=
        congrArg (originalTypedPairConverse S) hR.symm
      _ = taggedColour S (right r0) (right rLast) :=
        (original_actual_tagged_colour_converse S
          (right r0) (right rLast)).symm
  have hNe : left lK ≠ left l0 := by
    obtain ⟨a,ha⟩ := hChord
    have hsome :
        (taggedColour S (left lK) (left l0)).2.2.isSome = true := by
      have htag := congrArg
        (fun q : Σ i : ι, Σ j : ι, Option (S.Atom i j) => q.2.2.isSome) hL
      simpa only [originalTypedPairReading, ha, Option.isSome_some] using htag
    intro he
    rw [he] at hsome
    have hdiag :
        (taggedColour S (left l0) (left l0)).2.2.isSome = false := by
      cases h : left l0 with
      | mk sort point =>
          simp only [taggedColour,
            (S.colour_none_iff point point).mpr rfl, Option.isSome_none]
    rw [hdiag] at hsome
    cases hsome
  exact ⟨hSame,hNe⟩

end CCO.TypedOrbitFrames
