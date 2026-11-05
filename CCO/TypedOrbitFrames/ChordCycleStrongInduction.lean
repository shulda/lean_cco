import CCO.TypedOrbitFrames.RotateOldCycleHom
import CCO.TypedOrbitFrames.RotateSpecifiedChord
import CCO.TypedOrbitFrames.ChordShortRight

/-!
# B053 C04: strong induction over EVERY genuine OLD typed simple cycle

This is the exact combinatorial "all chords" induction used by source11.
It proves that the TWO explicit local mathematical obligations suffice:

* all genuine old typed chordless cycles have a true CycleHom;
* for a REAL original specified 0--k chord, the TWO actual shorter
  typed SimpleCycle homomorphisms glue to a CycleHom of the longer cycle.

Neither obligation is silently assumed to follow from Old SAP alone:
the second must be discharged via the genuine existing C03
finite-induced-image OLD SAP construction, while chordless clone-only
cycles require the source11 high-girth / STRONG-power argument.

An arbitrary chord s--t is normalized by the already proved
literal Fin/ZMod original-cycle rotation; the typed source diagram,
every old colour and the actual source vertex identities are kept.
The strong induction strictly decreases BOTH shorter cycle lengths.

Until the two explicitly named mathematical premises are supplied,
this is a CONDITIONAL receiving combinatorial induction, NOT the
source11 complete-base-chords export, orbit theorem or an HN result.
-/

namespace CCO.TypedOrbitFrames

universe u v w z
variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {V : Type z}

/-- A true old typed cycle has NO proper specified positive diversity
chord at ANY two nonconsecutive cyclic positions. This uses the
literal source PartialDiagram edge predicate, not graph completion. -/
def OriginalNoSpecifiedProperChord
    {D : PartialDiagram S V} (C : SimpleCycle D) : Prop :=
  letI : NeZero C.length := ⟨Nat.ne_of_gt C.length_pos⟩
  ∀ (s t : ZMod C.length),
    OriginalZModProperChord s t →
    ¬ OriginalArbitrarySpecifiedChord S C s t

/-- Source11 C04 combinatorial reduction: true realization of all
short triangles, all long chordless cycles, and the genuine
normalized one-chord old SAP gluing step imply realization of
EVERY actual typed SimpleCycle in the SAME old diagram.

The shorter realizations are not the conclusion disguised as a
hypothesis: they are supplied strictly inductively from lengths
k+1<n and n-k+1<n. The normalized gluing step receives exactly
those two short CycleHom proofs, with no long CycleHom premise. -/
theorem original_all_typed_cycles_from_proper_chord_induction
    (hTriangles : ∀ {D : PartialDiagram S V}
       (C : SimpleCycle D), C.length = 3 → CycleHom C)
    (hChordless : ∀ {D : PartialDiagram S V}
       (C : SimpleCycle D), 4 ≤ C.length →
       OriginalNoSpecifiedProperChord S C → CycleHom C)
    (hGlue : ∀ {D : PartialDiagram S V}
       (C : SimpleCycle D) {k : Nat}
       (cut : OriginalChordCut C.length k)
       (hChord : OriginalNormalizedSpecifiedChord S C cut),
       CycleHom (originalChordLeftShortCycle S C cut hChord) →
       CycleHom (originalChordRightShortCycle S C cut hChord) →
       CycleHom C) :
    ∀ {D : PartialDiagram S V} (C : SimpleCycle D), CycleHom C := by
  have hStrong :
      ∀ n : Nat, ∀ {D : PartialDiagram S V}
      (C : SimpleCycle D), C.length = n → CycleHom C := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
        intro D C hlen
        have hge : 3 ≤ n := by
          simpa only [hlen] using C.length_ge_three
        by_cases h3 : n = 3
        · exact hTriangles C (hlen.trans h3)
        have hn4 : 4 ≤ C.length := by
          rw [hlen]
          omega
        letI : NeZero C.length := ⟨Nat.ne_of_gt C.length_pos⟩
        by_cases hasChord :
            ∃ s t : ZMod C.length,
              OriginalZModProperChord s t ∧
              OriginalArbitrarySpecifiedChord S C s t
        · obtain ⟨s,t,hProper,hEdge⟩ := hasChord
          let cut : OriginalChordCut C.length (t - s).val :=
            original_zmod_proper_chord_has_cut hn4 s t hProper
          let rot : SimpleCycle D := originalRotateOldSimpleCycle S C s
          have hChord : OriginalNormalizedSpecifiedChord S rot cut :=
            original_arbitrary_specified_chord_rotates
              S C hn4 s t hProper hEdge
          have hshort := original_chord_both_cycles_shorter cut
          have hleft :
              CycleHom (originalChordLeftShortCycle S rot cut hChord) := by
            apply ih ((t - s).val + 1)
            · simpa only [← hlen] using hshort.1
            · rfl
          have hright :
              CycleHom (originalChordRightShortCycle S rot cut hChord) := by
            apply ih (C.length - (t - s).val + 1)
            · simpa only [← hlen] using hshort.2
            · rfl
          have hrot : CycleHom rot :=
            hGlue rot cut hChord hleft hright
          exact (original_rotate_old_cycle_hom_iff S C s).mp hrot
        · have hNo : OriginalNoSpecifiedProperChord S C := by
            intro s t hProper hEdge
            exact hasChord ⟨s,t,hProper,hEdge⟩
          exact hChordless C hn4 hNo
  intro D C
  exact hStrong C.length C rfl

end CCO.TypedOrbitFrames
