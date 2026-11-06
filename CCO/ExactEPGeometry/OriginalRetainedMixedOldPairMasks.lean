import CCO.APCharacter.MaskReadout
import CCO.APCharacter.SourceAge.SingleStep

/-!
# B062 C96: exact active/inactive decomposition of REAL old marked pair masks

For one actual full source SourcePhase, every inactive named parent has
exactly the forced bit zero and contributes NO binary phase condition:
the original mask on an old pair with either endpoint inactive is
already automatic from the two unary validBit conditions. Thus whole
old-pair legality of an arbitrary (possibly mixed active/inactive)
family is precisely (1) all actual unary valid bits and (2) pairwise
legality on pairs whose BOTH parent sorts are genuinely reached.

This is a real source-side C96 reduction, NOT yet the full selected
quotient marked-age converse; relating arbitrary selected old pair
representatives to the COMPLETE projected Arrow conditions remains
separately necessary. No quotient SAP, automorphism section, old
global marking or invented quotient orbit is assumed.
-/

universe u v w t z

namespace CCO.ExactEPGeometry

open APCharacter
open APCharacter.Towers
open RigidGroupoid.Geometry

noncomputable section

/-- C96 source-side, including all mixed reached/inactive pairs,
true logical diagonals, and arbitrary families (not just finite).
Whole old pair legality is exactly unary bit validity plus pair
legality on pairs of actually reached parents. -/
theorem originalRetainedMixedOldPairMasks_iff
    (B : CurrentSource.{u,v,w,t})
    {r : B.Sorts} (Kroot : Kernel B.source r)
    (phase : SourcePhase B.source B.homogeneous
      (exactCalculus_of_homogeneous_CCO
        B.source B.homogeneous B.cco) Kroot)
    {V : Type z} (point : V → Sigma B.Point)
    (bits : V → ZMod 2) :
    (∀ i j : V,
      phase.allows (B.source.colour (point i).2 (point j).2)
        (bits i) (bits j)) ↔
    (∀ i : V, phase.validBit (point i).1 (bits i)) ∧
    (∀ i j : V,
      Nonempty (Bridge B.source Kroot (point i).1) →
      Nonempty (Bridge B.source Kroot (point j).1) →
      phase.allows (B.source.colour (point i).2 (point j).2)
        (bits i) (bits j)) := by
  constructor
  · intro h
    constructor
    · intro i
      exact (h i i).1
    · intro i j _ _
      exact h i j
  · rintro ⟨hValid,hActive⟩ i j
    by_cases hi : Nonempty (Bridge B.source Kroot (point i).1)
    · by_cases hj : Nonempty (Bridge B.source Kroot (point j).1)
      · exact hActive i j hi hj
      · exact phase.inactive_masks_full
          (bits i) (bits j) (hValid i) (hValid j)
          (Or.inr hj) (B.source.colour (point i).2 (point j).2)
    · exact phase.inactive_masks_full
        (bits i) (bits j) (hValid i) (hValid j)
        (Or.inl hi) (B.source.colour (point i).2 (point j).2)

/-- C96 source-side converse readout: any genuine globally
SourcePhase-legal old marking forces ZERO on every actual
inactive old parent, including its real points in old E classes. -/
theorem originalRetainedGlobalMarkInactive_zero
    (B : CurrentSource.{u,v,w,t})
    {r : B.Sorts} (Kroot : Kernel B.source r)
    (phase : SourcePhase B.source B.homogeneous
      (exactCalculus_of_homogeneous_CCO
        B.source B.homogeneous B.cco) Kroot)
    (mark : Sigma B.Point → ZMod 2)
    (hMark : phase.masks.GlobalMarking mark)
    (i : B.Sorts)
    (hInactive : ¬Nonempty (Bridge B.source Kroot i))
    (x : B.Point i) :
    mark ⟨i,x⟩ = 0 := by
  exact (hMark.1 (⟨i,x⟩ : Sigma B.Point)) hInactive

end
end CCO.ExactEPGeometry
