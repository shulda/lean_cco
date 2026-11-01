import CCO.ExactEPGeometry.OriginalOccupancyOrbitals
import CCO.RigidGroupoid.Geometry.ProjectedKernels

/-!
# B062 C72: two DIFFERENT genuine quotient identity pullbacks

On the already constructed actual selected-occupancy quotient prefix,
a point of sort c is the literal class in p_c / (E|p_c²).
Consequently its LOGICAL equality pulls back to the whole actual
current E-kernel e_p; it must not be confused with the original
logical identity of distinct points within an E-class.

If a current full-exact gate K contains e_p, the relation induced by
the COMPLETE gate on these actual quotient classes pulls back to
the WHOLE K relation, not merely e_p or pointwise identity. This is
the exact relational identity used by the source projected groupoid;
the additional *quotient* full RAW exactness of a projected K remains
a separate provider obligation (C82), not asserted here.

No SAP, invented quotient group section, original-diversity copy of
identity, or reverse exact descent on arbitrary mixed source sorts.
-/

universe u v w t

namespace CCO.ExactEPGeometry

open APCharacter.Towers
open RigidGroupoid.Geometry

noncomputable section

/-- The REAL quotient projection onto a selected occupancy parent.
This is an actual quotient of the local old-E restriction, never a
choice of one point from each quotient E-class. -/
def selectedOccupancyQuotientProjection
    (A B : CurrentSource.{u,v,w,t})
    (P : UnaryReduct A.source B.source)
    (transport : ExactTraceTransport A.source B.source P)
    (base : A.Sorts) (hOne : ∀ i : A.Sorts, base = i)
    (E : ExactEq A.source base)
    (c : OriginalOccupancy A B P base hOne E) :
    B.Point (originalOccupancyRepresentative A B P base hOne E c) →
      (originalExactSelectedQuotientCurrentSource
        A B P transport base hOne E).Point c :=
  fun x => Quotient.mk'' x

/-- Source C72 logical QUOTIENT identity: the whole pullback of
quotient equality is EXACTLY the current old-E kernel, including
distinct real representatives of the same E-class. -/
theorem selectedOccupancyQuotientIdentity_iff
    (A B : CurrentSource.{u,v,w,t})
    (P : UnaryReduct A.source B.source)
    (transport : ExactTraceTransport A.source B.source P)
    (base : A.Sorts) (hOne : ∀ i : A.Sorts, base = i)
    (E : ExactEq A.source base)
    (c : OriginalOccupancy A B P base hOne E)
    (x y : B.Point (originalOccupancyRepresentative A B P base hOne E c)) :
    let π := selectedOccupancyQuotientProjection
      A B P transport base hOne E c
    π x = π y ↔
      (originalExactOnCurrentSort A B P transport base hOne E
        (originalOccupancyRepresentative A B P base hOne E c)) x y := by
  dsimp only
  exact Quotient.eq

/-- In the actual original one-sort source, quotient equality pulls
back to the ORIGINAL E on the real projected old points (both points
belong to the SAME current selected parent). This distinguishes
quotient Id from the ORIGINAL logical equality relation. -/
theorem selectedOccupancyQuotientIdentity_original_iff
    (A B : CurrentSource.{u,v,w,t})
    (P : UnaryReduct A.source B.source)
    (transport : ExactTraceTransport A.source B.source P)
    (base : A.Sorts) (hOne : ∀ i : A.Sorts, base = i)
    (E : ExactEq A.source base)
    (c : OriginalOccupancy A B P base hOne E)
    (x y : B.Point (originalOccupancyRepresentative A B P base hOne E c)) :
    let π := selectedOccupancyQuotientProjection
      A B P transport base hOne E c
    π x = π y ↔
      E ((hOne (P.parent (originalOccupancyRepresentative
            A B P base hOne E c))).symm ▸
          P.point (originalOccupancyRepresentative A B P base hOne E c) x)
        ((hOne (P.parent (originalOccupancyRepresentative
            A B P base hOne E c))).symm ▸
          P.point (originalOccupancyRepresentative A B P base hOne E c) y) := by
  dsimp only
  exact (selectedOccupancyQuotientIdentity_iff
    A B P transport base hOne E c x y).trans
    ((PrefixExactRestriction.rho_iff A B P transport
      (originalOccupancyRepresentative A B P base hOne E c)
      (oldExactEqCast A.source
        (hOne (P.parent (originalOccupancyRepresentative
          A B P base hOne E c))).symm E) x y).trans
      (oldExactEqCast_iff A.source
        (hOne (P.parent (originalOccupancyRepresentative
          A B P base hOne E c))).symm E
        (P.point (originalOccupancyRepresentative A B P base hOne E c) x)
        (P.point (originalOccupancyRepresentative A B P base hOne E c) y)))

/-- C72 GROUPoid gate identity is different from quotient equality.
If e_p≤K is an actual current full-exact gate above the local old-E
kernel, the WHOLE projected K relation on the real quotient sort
pulls back to precisely K, not merely e_p. No quotient full-exact
property is assumed or deduced for the projected gate here. -/
theorem selectedOccupancyProjectedGate_pullback
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
          K.rel x y) :
    let π := selectedOccupancyQuotientProjection
      A B P transport base hOne E c
    GroupActions.pullback π π (Quotient.image π π K.rel) = K.rel := by
  dsimp only
  let π := selectedOccupancyQuotientProjection
    A B P transport base hOne E c
  have hKernel : ∀ x y, π x = π y → K.rel x y := by
    intro x y hxy
    exact hNested x y ((selectedOccupancyQuotientIdentity_iff
      A B P transport base hOne E c x y).mp hxy)
  funext x y
  apply propext
  constructor
  · rintro ⟨a,b,ha,hb,hab⟩
    exact K.setoid.trans (hKernel x a ha.symm)
      (K.setoid.trans hab (hKernel b y hb))
  · intro hxy
    exact ⟨x,y,rfl,rfl,hxy⟩

end
end CCO.ExactEPGeometry
