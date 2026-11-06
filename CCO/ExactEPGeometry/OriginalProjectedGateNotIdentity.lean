import CCO.ExactEPGeometry.OriginalQuotientIdentities

/-!
# B062 C111: the true quotient logical Id differs from the full gate Id

At an ACTUAL selected original E occupancy parent c, the quotient
carrier is the literal E|p² class space, and the quotient equality
pullback is the whole E kernel, not old point equality. If the real
full current gate K STRICTLY contains E|p², some distinct E-classes
are related by the projected FULL gate Arrow, even though they are
not LOGICALLY equal as quotient points.

The first fact is the already proved genuine C72 identity pullback;
the second is a real witness excluding the invalid shortcut
"whole groupoid identity = logical identity". No quotient SAP,
group section or mixed RAW reverse exact descent is assumed.
-/

universe u v w t

namespace CCO.ExactEPGeometry

open APCharacter.Towers
open RigidGroupoid.Geometry

noncomputable section

/-- Source C111 strictly distinguishes the actual complete projected
gate relation from quotient logical equality whenever E is strictly
smaller than K: their real pullbacks are E and K respectively.
The strictness premise is EXACTLY K≰E, not a positive extra
hypothesis unrelated to the source quotient. -/
theorem selectedOccupancy_projectedGate_differs_from_identity
    (A B : CurrentSource.{u,v,w,t})
    (P : UnaryReduct A.source B.source)
    (transport : ExactTraceTransport A.source B.source P)
    (base : A.Sorts) (hOne : ∀ i : A.Sorts, base = i)
    (E : ExactEq A.source base)
    (c : OriginalOccupancy A B P base hOne E)
    (K : Kernel B.source
      (originalOccupancyRepresentative A B P base hOne E c))
    (hNested : ∀ x y,
      (originalExactOnCurrentSort A B P transport base hOne E
        (originalOccupancyRepresentative A B P base hOne E c)) x y →
      K.rel x y)
    (hStrict : ¬∀ x y, K.rel x y →
      (originalExactOnCurrentSort A B P transport base hOne E
        (originalOccupancyRepresentative A B P base hOne E c)) x y) :
    let π := selectedOccupancyQuotientProjection
      A B P transport base hOne E c
    GroupActions.pullback π π (Quotient.image π π K.rel) = K.rel ∧
      ∃ x y : B.Point
        (originalOccupancyRepresentative A B P base hOne E c),
        Quotient.image π π K.rel (π x) (π y) ∧ π x ≠ π y := by
  let π := selectedOccupancyQuotientProjection
    A B P transport base hOne E c
  have hPull :=
    selectedOccupancyProjectedGate_pullback
      A B P transport base hOne E c K hNested
  constructor
  · exact hPull
  · push_neg at hStrict
    obtain ⟨x,y,hK,hE⟩ := hStrict
    refine ⟨x,y,⟨x,y,rfl,rfl,hK⟩,?_⟩
    intro hEq
    exact hE ((selectedOccupancyQuotientIdentity_iff
      A B P transport base hOne E c x y).mp hEq)

end
end CCO.ExactEPGeometry
