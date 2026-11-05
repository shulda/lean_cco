import CCO.TypedOrbitFrames.TypedChordlessBase

/-!
# Source11 C04: genuine old cycle reduction inside one fixed diagram

The induction keeps the original partial diagram fixed. Its local triangle
and chordless witnesses are therefore needed only in the source diagram
being tested, rather than in every arbitrary old partial diagram.

The old chord step uses actual shorter cycle homomorphisms, original pair
homogeneity and SAP of their finite induced images. The complete-base
specialization tests exactly triangles meeting the base and chordless
clone-only cycles. It does not supply a whole-diagram CCO homomorphism.
-/

namespace CCO.TypedOrbitFrames

universe u v w z t r
variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {G : Type r} [Group G] [∀ i : ι, MulAction G (X i)]

/-- All cyclic chord splitting and original old SAP gluing are discharged
inside the SAME partial diagram. No realizability premise is imposed on
unrelated partial diagrams, and neither recursive premise is the long-cycle
conclusion itself. -/
theorem original_all_typed_cycles_in_diagram_of_old_chordless_cases
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    {V : Type z} (D : PartialDiagram S V)
    (hTriangles : ∀ C : SimpleCycle D, C.length = 3 → CycleHom C)
    (hChordless : ∀ C : SimpleCycle D, 4 ≤ C.length →
      OriginalNoSpecifiedProperChord S C → CycleHom C) :
    ∀ C : SimpleCycle D, CycleHom C := by
  have hStrong : ∀ n : Nat, ∀ C : SimpleCycle D,
      C.length = n → CycleHom C := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
        intro C hlen
        have hge : 3 ≤ n := by
          simpa only [hlen] using C.length_ge_three
        by_cases h3 : n = 3
        · exact hTriangles C (hlen.trans h3)
        have hn4 : 4 ≤ C.length := by rw [hlen]; omega
        letI : NeZero C.length := ⟨Nat.ne_of_gt C.length_pos⟩
        by_cases hasChord : ∃ s t : ZMod C.length,
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
            original_normalized_chord_glue_actual_short_homs
              S H sap rot cut hChord hleft hright
          exact (original_rotate_old_cycle_hom_iff S C s).mp hrot
        · exact hChordless C hn4 (by
            intro s t hProper hEdge
            exact hasChord ⟨s,t,hProper,hEdge⟩)
  intro C
  exact hStrong C.length C rfl

/-- A triangle has no proper nonconsecutive cyclic positions at all.
In particular it is genuinely chordless in its original typed diagram. -/
theorem original_triangle_has_no_specified_proper_chord
    {V : Type z} {D : PartialDiagram S V}
    (C : SimpleCycle D) (h3 : C.length = 3) :
    OriginalNoSpecifiedProperChord S C := by
  letI : NeZero C.length := ⟨Nat.ne_of_gt C.length_pos⟩
  intro s t hProper _
  obtain ⟨hne,hforward,hbackward⟩ := hProper
  have hlt : (t - s).val < 3 := by
    simpa only [h3] using ZMod.val_lt (t - s)
  have hzero : (t - s).val ≠ 0 := by
    intro hz
    exact hne (sub_eq_zero.mp ((ZMod.val_eq_zero (t - s)).mp hz))
  have hone : (t - s).val ≠ 1 := by
    intro hz
    have hd : t - s = (1 : ZMod C.length) :=
      (ZMod.val_eq_one (by omega : 1 < C.length) (t - s)).mp hz
    apply hforward
    calc
      t = (t - s) + s := by abel
      _ = 1 + s := by rw [hd]
      _ = s + 1 := by abel
  have htwo : (t - s).val = 2 := by omega
  have hneg : (-1 : ZMod C.length).val = 2 := by
    rw [h3]
    exact ZMod.val_neg_one 2
  have hd : t - s = -1 :=
    (ZMod.val_injective C.length) (htwo.trans hneg.symm)
  apply hbackward
  calc
    s = t - (t - s) := by abel
    _ = t - (-1) := by rw [hd]
    _ = t + 1 := by abel

/-- Source11 complete-base cycle test in its literal typed diagram:
only triangles meeting the complete old base and chordless cycles entirely
inside the clones need old homomorphisms. Original old SAP supplies every
chord-gluing step. Missing clone edges remain unassigned throughout. -/
theorem original_complete_base_cycle_hom_of_local_tests
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    {B : Type z} {Y : Type t}
    (D : PartialDiagram S (B ⊕ Y))
    (hBase : OriginalCompleteBaseSpokes S D)
    (hBaseTriangles : ∀ C : SimpleCycle D, C.length = 3 →
      (∃ p : Fin C.length, ∃ d : B, C.vertices p = Sum.inl d) →
      CycleHom C)
    (hCloneChordless : ∀ C : SimpleCycle D,
      OriginalNoSpecifiedProperChord S C →
      (∀ p : Fin C.length, ∃ y : Y, C.vertices p = Sum.inr y) →
      CycleHom C) :
    ∀ C : SimpleCycle D, CycleHom C := by
  apply original_all_typed_cycles_in_diagram_of_old_chordless_cases S H sap D
  · intro C h3
    by_cases hTouches : ∃ p : Fin C.length, ∃ d : B,
        C.vertices p = Sum.inl d
    · exact hBaseTriangles C h3 hTouches
    · apply hCloneChordless C
        (original_triangle_has_no_specified_proper_chord S C h3)
      intro p
      cases hv : C.vertices p with
      | inl d => exact False.elim (hTouches ⟨p,d,hv⟩)
      | inr y => exact ⟨y,hv⟩
  · intro C h4 hNo
    exact hCloneChordless C hNo
      (original_typed_complete_base_chordless_only_clones S D hBase C h4 hNo)

end CCO.TypedOrbitFrames
