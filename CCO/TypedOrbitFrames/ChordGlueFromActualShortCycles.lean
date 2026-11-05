import CCO.TypedOrbitFrames.ShortChordPairMatch
import CCO.TypedOrbitFrames.TaggedChordSAP
import CCO.TypedOrbitFrames.ChordSplitSideReading

/-!
# B053 C04: unconditional original OLD SAP normalized chord induction STEP

Two true strictly shorter old typed SimpleCycle objects are constructed
from the SAME source PartialDiagram and its specified diversity chord.
Assume their genuinely recursively supplied CycleHom witnesses; then
read both full original typed side colours, identify their CLOSING
chord pair in a common k-to-zero orientation, and invoke the
already proven genuine original finite-induced-image AgeSAP bridge.

The single resulting old target tuple preserves EVERY original
cyclic side colour via the already proved exact arc-cover
and map-gluing lemmas, and hence is a genuine CycleHom of the
original longer SimpleCycle. There is no hypothetical long-cycle
CycleHom premise, hidden SAP, or arbitrary CCO completion.

The following source11 theorem can therefore discharge the
hGlue parameter of ChordCycleStrongInduction. Realization of
the actual old typed chordless source cycles remains its distinct
mathematical CCO/power/triangle input; it is NOT silently asserted.
-/

namespace CCO.TypedOrbitFrames

universe u v w z t
variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {V : Type z}
variable {G : Type t} [Group G] [∀ i : ι, MulAction G (X i)]

/-- The two actual TRUE shorter old CycleHom proofs can be
amalgamated via the original age SAP and one chord automorphism
to obtain the long-cycle old homomorphism. This discharges the
C04 one-chord induction step without replacing the conclusion
by a new hypothesis. -/
theorem original_normalized_chord_glue_actual_short_homs
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    {D : PartialDiagram S V} (C : SimpleCycle D)
    {k : Nat} (cut : OriginalChordCut C.length k)
    (hChord : OriginalNormalizedSpecifiedChord S C cut)
    (hLeft : CycleHom (originalChordLeftShortCycle S C cut hChord))
    (hRight : CycleHom (originalChordRightShortCycle S C cut hChord)) :
    CycleHom C := by
  let L : SimpleCycle D := originalChordLeftShortCycle S C cut hChord
  let R : SimpleCycle D := originalChordRightShortCycle S C cut hChord
  obtain ⟨left,hReadL⟩ :=
    original_cycle_hom_has_tagged_side_reading S L hLeft
  obtain ⟨right,hReadR⟩ :=
    original_cycle_hom_has_tagged_side_reading S R hRight
  obtain ⟨hSame,hNe⟩ :=
    original_short_cycles_same_full_chord_reading
      S C cut hChord left right hReadL hReadR
  let lK : Fin (k+1) :=
    ⟨k, by have hc := cut.left_nontrivial; omega⟩
  let l0 : Fin (k+1) := ⟨0, by omega⟩
  let r0 : Fin (C.length-k+1) :=
    ⟨0, by have hc := cut.right_nontrivial; omega⟩
  let rLast : Fin (C.length-k+1) :=
    ⟨C.length-k, by omega⟩
  obtain ⟨M,fl,gr,hMemL,hMemR,hColL,hColR,hK,h0⟩ :=
    original_old_tuples_matching_tagged_chord_sap
      S H sap left right lK l0 r0 rLast hSame hNe
  have hLside : ∀ a b : Fin (k+1), a.val + 1 = b.val →
      taggedColour S (fl a) (fl b) =
        originalSpecifiedCycleSideReading S C
          (originalChordLeftIndex cut a) := by
    intro a b hab
    have hNext : b = CCO.cyclicNext L.length_pos a := by
      apply Fin.ext
      change b.val = (a.val + 1) % (k+1)
      rw [hab, Nat.mod_eq_of_lt b.isLt]
    have ha : a.val < k := by have hb := b.isLt; omega
    calc
      taggedColour S (fl a) (fl b) =
          taggedColour S (left a) (left b) := hColL a b
      _ = taggedColour S (left a)
          (left (CCO.cyclicNext L.length_pos a)) :=
        congrArg (fun p : Fin (k+1) => taggedColour S (left a) (left p)) hNext
      _ = originalSpecifiedCycleSideReading S L a := hReadL a
      _ = originalSpecifiedCycleSideReading S C
          (originalChordLeftIndex cut a) :=
        original_left_short_internal_tagged_reading
          S C cut hChord a ha
  have hRside : ∀ a b : Fin (C.length-k+1),
      a.val + 1 = b.val →
      taggedColour S (gr a) (gr b) =
        originalSpecifiedCycleSideReading S C
          (originalChordRightIndex cut a) := by
    intro a b hab
    have hNext : b = CCO.cyclicNext R.length_pos a := by
      apply Fin.ext
      change b.val = (a.val + 1) % (C.length-k+1)
      rw [hab, Nat.mod_eq_of_lt b.isLt]
    have ha : a.val < C.length-k := by
      have hb := b.isLt
      omega
    calc
      taggedColour S (gr a) (gr b) =
          taggedColour S (right a) (right b) := hColR a b
      _ = taggedColour S (right a)
          (right (CCO.cyclicNext R.length_pos a)) :=
        congrArg
          (fun p : Fin (C.length-k+1) => taggedColour S (right a) (right p))
          hNext
      _ = originalSpecifiedCycleSideReading S R a := hReadR a
      _ = originalSpecifiedCycleSideReading S C
          (originalChordRightIndex cut a) :=
        original_right_short_internal_tagged_reading
          S C cut hChord a ha
  let whole : Fin C.length → Sigma X :=
    originalChordGlue cut fl gr
  have hEvery : ∀ p : Fin C.length,
      taggedColour S (whole p)
        (whole (CCO.cyclicNext C.length_pos p)) =
          originalSpecifiedCycleSideReading S C p :=
    original_chord_glue_preserves_all_old_cycle_sides
      S cut fl gr (originalSpecifiedCycleSideReading S C)
      hK h0 hLside hRside
  exact original_coloured_side_reading_is_cycle_hom
    S C whole hEvery

/-- Source11 C04 without any remaining chord-gluing hypothesis.
It requires ONLY a TRUE old CycleHom for each chordless cycle
(and the separately genuine old triangles); all cyclic chord
splitting, short source construction, old image SAP, original
pair homogeneity and arbitrary rotation are now discharged. -/
theorem original_all_typed_cycles_of_old_chordless_cases
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    (hTriangles : ∀ {D : PartialDiagram S V}
      (C : SimpleCycle D), C.length = 3 → CycleHom C)
    (hChordless : ∀ {D : PartialDiagram S V}
      (C : SimpleCycle D), 4 ≤ C.length →
      OriginalNoSpecifiedProperChord S C → CycleHom C) :
    ∀ {D : PartialDiagram S V} (C : SimpleCycle D), CycleHom C := by
  exact original_all_typed_cycles_from_proper_chord_induction
    S hTriangles hChordless
    (by
      intro D C k cut hChord hL hR
      exact original_normalized_chord_glue_actual_short_homs
        S H sap C cut hChord hL hR)

end CCO.TypedOrbitFrames
