import CCO.ExactEPGeometry.OriginalSelectedFiniteLocalMarkedAge
import CCO.APCharacter.MaskReadout

/-!
# B062 C96: actual mixed active/inactive quotient-point marking realization

Take ANY finite family of distinct already-realized points in the
genuine one-parent-per-original-E-occupancy selected quotient source,
including a mixture of reached and inactive parent sorts. Give every
point its ACTUAL old representative, with the entire old fine orbital
table and old logical diagonal.

Suppose ONE real globally source-legal old marking realizes every
prescribed bit on reached representatives, and the prescribed bit on
every inactive representative is the genuine forced zero. This is
ENOUGH to embed the FULL mixed old finite marked chart in the
actual SourcePhase homogeneous successor. Pair masks touching
inactive sorts are automatic; reached-reached pairs use the
same globally legal old mark.

The existence of the required global marking from arbitrary locally
admissible quotient orbital diagrams is a distinct C88/C93–C96
obligation. This theorem does not invent SAP, quotient group sections,
new fine old colours or hypothetical embedded quotient charts.
-/

universe u v w t

namespace CCO.ExactEPGeometry

open APCharacter
open APCharacter.Towers
open RigidGroupoid.Geometry
open OwnerTransversal.CountableColour

noncomputable section

/-- C96: a genuine finite mixed selected E-quotient configuration
with one global legal old marking on reached points and the forced
inactive zero bits has a real induced embedding into the full
AP-only marked successor, preserving ALL old fine pair names.
No quotient SAP, assumed output homogeneity or group section. -/
theorem originalSelectedFiniteMixedMarkedOldAge_names
    (A B : CurrentSource.{u,v,w,t})
    (P : UnaryReduct A.source B.source)
    (transport : ExactTraceTransport A.source B.source P)
    (base : A.Sorts) (hOne : ∀ i : A.Sorts, base = i)
    (E : ExactEq A.source base)
    {r : B.Sorts} (Kroot : Kernel B.source r)
    (phase : SourcePhase B.source B.homogeneous
      (exactCalculus_of_homogeneous_CCO
        B.source B.homogeneous B.cco) Kroot)
    {n : Nat}
    (points : Fin n ↪ Sigma
      (originalExactSelectedQuotientCurrentSource
        A B P transport base hOne E).Point)
    (bits : Fin n → ZMod 2)
    (hGlobal :
      let old : Fin n → Sigma B.Point := fun i =>
        originalSelectedTaggedRepresentative
          A B P transport base hOne E (points i)
      ∃ mark : Sigma B.Point → ZMod 2,
        phase.masks.GlobalMarking mark ∧
        (∀ i : Fin n,
          Nonempty (Bridge B.source Kroot (old i).1) →
            mark (old i) = bits i) ∧
        (∀ i : Fin n,
          ¬Nonempty (Bridge B.source Kroot (old i).1) →
            bits i = 0)) :
    let old : Fin n → Sigma B.Point := fun i =>
      originalSelectedTaggedRepresentative
        A B P transport base hOne E (points i)
    ∃ f : Fin n ↪ phase.MarkedLimit B.cco,
      (∀ i, (phase.markedCoding B.cco).table.owner (f i) =
        APCharacter.Age.ownerEquiv B.source ((old i).1,bits i)) ∧
      ∀ i j, (phase.markedCoding B.cco).table.colour (f i) (f j) =
        APCharacter.Age.colourEquiv B.source
          (taggedColour B.source (old i) (old j)) := by
  let old : Fin n → Sigma B.Point := fun i =>
    originalSelectedTaggedRepresentative
      A B P transport base hOne E (points i)
  obtain ⟨mark,hMark,hActive,hInactive⟩ := hGlobal
  have hValid : ∀ i : Fin n,
      phase.masks.validBit (old i).1 (bits i) := by
    intro i
    by_cases hi : Nonempty (Bridge B.source Kroot (old i).1)
    · have hv := hMark.1 (old i)
      rw [hActive i hi] at hv
      exact hv
    · change ¬Nonempty (Bridge B.source Kroot (old i).1) → bits i = 0
      intro _
      exact hInactive i hi
  have hPairs : ∀ i j : Fin n,
      phase.masks.allowed
        (B.source.colour (old i).2 (old j).2)
        (bits i) (bits j) := by
    intro i j
    by_cases hi : Nonempty (Bridge B.source Kroot (old i).1)
    · by_cases hj : Nonempty (Bridge B.source Kroot (old j).1)
      · have h := hMark.2 (old i) (old j)
        have ha : mark (old i) = bits i := hActive i hi
        have hb : mark (old j) = bits j := hActive j hj
        rw [ha,hb] at h
        exact h
      · exact phase.inactive_masks_full
          (bits i) (bits j) (hValid i) (hValid j)
          (Or.inr hj) (B.source.colour (old i).2 (old j).2)
    · exact phase.inactive_masks_full
        (bits i) (bits j) (hValid i) (hValid j)
        (Or.inl hi) (B.source.colour (old i).2 (old j).2)
  exact originalSelectedFiniteLocalMarkedAge_names
    A B P transport base hOne E Kroot phase
      points bits hValid hPairs

end
end CCO.ExactEPGeometry
