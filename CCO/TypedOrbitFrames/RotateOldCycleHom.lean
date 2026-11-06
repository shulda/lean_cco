import CCO.TypedOrbitFrames.RotateOldSideReading

/-!
# B053 source11 C04: old typed CycleHom is invariant under actual rotation

The finite old-source rotation is bijective and commutes with the
literal cyclic successor. Its CCO.SimpleCycle side readings are
the genuine old typed partial-diagram edge certificates, not
colourings of an unlabelled graph.

Thus a TRUE old CycleHom of the rotated source is equivalent
to a TRUE old CycleHom of the original source, in both directions.
This allows normalising an arbitrary-position chord to 0--k
without assuming a realisation of the original long cycle.
-/

namespace CCO.TypedOrbitFrames

universe u v w z
variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {V : Type z}

/-- Rotating the source formal vertices and every specified old
typed atomic side gives an EQUIVALENT actual CycleHom predicate.
The reverse direction genuinely uses the inverse rotation,
so it does not treat an injection as surjective without proof. -/
theorem original_rotate_old_cycle_hom_iff
    {D : PartialDiagram S V} (C : SimpleCycle D)
    (s : ZMod C.length) :
    CycleHom (originalRotateOldSimpleCycle S C s) ↔ CycleHom C := by
  letI : NeZero C.length := ⟨Nat.ne_of_gt C.length_pos⟩
  constructor
  · intro hrot
    obtain ⟨f, hf⟩ :=
      original_cycle_hom_has_tagged_side_reading
        S (originalRotateOldSimpleCycle S C s) hrot
    apply (original_cycle_hom_iff_tagged_side_reading S C).mpr
    refine ⟨fun p => f (originalCycleRotateIndex (-s) p), ?_⟩
    intro p
    have hn := original_cycle_rotate_next C.length_ge_three (-s) p
    have hside :
        originalSpecifiedCycleSideReading S
            (originalRotateOldSimpleCycle S C s)
            (originalCycleRotateIndex (-s) p) =
          originalSpecifiedCycleSideReading S C p := by
      rw [original_rotated_old_cycle_side_reading S C s
        (originalCycleRotateIndex (-s) p),
        original_cycle_rotate_inverse_index]
    calc
      taggedColour S
          (f (originalCycleRotateIndex (-s) p))
          (f (originalCycleRotateIndex (-s)
            (CCO.cyclicNext C.length_pos p))) =
          taggedColour S
            (f (originalCycleRotateIndex (-s) p))
            (f (CCO.cyclicNext C.length_pos
              (originalCycleRotateIndex (-s) p))) := by rw [hn] <;> rfl
      _ = originalSpecifiedCycleSideReading S
          (originalRotateOldSimpleCycle S C s)
          (originalCycleRotateIndex (-s) p) :=
            hf (originalCycleRotateIndex (-s) p)
      _ = originalSpecifiedCycleSideReading S C p := hside
  · intro horig
    obtain ⟨f, hf⟩ := original_cycle_hom_has_tagged_side_reading S C horig
    apply (original_cycle_hom_iff_tagged_side_reading S
      (originalRotateOldSimpleCycle S C s)).mpr
    refine ⟨fun p => f (originalCycleRotateIndex s p), ?_⟩
    intro p
    have hn := original_cycle_rotate_next C.length_ge_three s p
    calc
      taggedColour S
          (f (originalCycleRotateIndex s p))
          (f (originalCycleRotateIndex s
            (CCO.cyclicNext C.length_pos p))) =
          taggedColour S
            (f (originalCycleRotateIndex s p))
            (f (CCO.cyclicNext C.length_pos
              (originalCycleRotateIndex s p))) := by rw [hn] <;> rfl
      _ = originalSpecifiedCycleSideReading S C
          (originalCycleRotateIndex s p) :=
            hf (originalCycleRotateIndex s p)
      _ = originalSpecifiedCycleSideReading S
          (originalRotateOldSimpleCycle S C s) p :=
            (original_rotated_old_cycle_side_reading S C s p).symm

end CCO.TypedOrbitFrames
