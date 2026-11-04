import CCO.TypedOrbitFrames.CycleHomReading

/-!
# B053 C04: exact typed cyclic readings in BOTH directions

The previous source11 receiving lemma turns a complete optional
old pair-colour reading of every directed side of an actual
`CCO.SimpleCycle` into `CCO.CycleHom`.

Here we prove the converse FROM the actual homogeneous source
`CycleHom` witnesses, so shorter-cycle realization is never
replaced by an arbitrary abstract colouring oracle. The witness
uses the original named sort at each actual formal cycle vertex
and retains the true old diversity atom on each specified edge;
there is no global injectivity requirement.
-/

universe u v w z
namespace CCO.TypedOrbitFrames

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {V : Type z}

/-- A genuine source-cycle homomorphism gives a Sigma-valued
literal old sort and FULL typed side-colour reading, including
the actual optional diversity colour on every specified side. -/
theorem original_cycle_hom_has_tagged_side_reading
    {D : PartialDiagram S V} (C : SimpleCycle D)
    (h : CycleHom C) :
    ∃ f : Fin C.length → Sigma X,
      ∀ p : Fin C.length,
        taggedColour S (f p)
          (f (CCO.cyclicNext C.length_pos p)) =
          originalSpecifiedCycleSideReading S C p := by
  obtain ⟨point, hPoint⟩ := h
  refine ⟨fun p => ⟨D.vertexSort (C.vertices p), point p⟩, ?_⟩
  intro p
  obtain ⟨a, ha⟩ := C.specified p
  have hc := hPoint p a ha
  simp only [taggedColour, originalSpecifiedCycleSideReading, hc, ha]

/-- Source-specific binary exactness: a cycle is homomorphically
realizable if and only if one actual old typed Sigma tuple reads
EVERY specified side with the original tagged atomic colour.
The two directions have separate verified Lean proofs, rather
than a conditional provider consisting of the same conclusion. -/
theorem original_cycle_hom_iff_tagged_side_reading
    {D : PartialDiagram S V} (C : SimpleCycle D) :
    CycleHom C ↔
      ∃ f : Fin C.length → Sigma X,
        ∀ p : Fin C.length,
          taggedColour S (f p)
            (f (CCO.cyclicNext C.length_pos p)) =
            originalSpecifiedCycleSideReading S C p := by
  constructor
  · exact original_cycle_hom_has_tagged_side_reading S C
  · rintro ⟨f, hf⟩
    exact original_coloured_side_reading_is_cycle_hom S C f hf

end CCO.TypedOrbitFrames
