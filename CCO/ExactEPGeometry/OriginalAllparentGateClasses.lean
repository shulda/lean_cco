import CCO.ExactEPGeometry.ProjectedGateClassEquiv
import CCO.ExactEPGeometry.OriginalCoherentAllparentGroupoid

/-!
# B062 C82/C86/C93: ACTUAL original-gate classes and coherent E-quotient gates

For any original full exact E, any genuine current gate K with the
PROVED local E≤K, the genuine all-parent simultaneous typed quotient
constructed in C67 carries the actual projected full-RAW-exact K/E
kernel from C82. Every K-class has exactly one K/E-class and vice versa.
This is the real source application of the generic quotient class
equivalence; it does not assert an arbitrary mixed reverse exact
descent or an automorphism-group section.

Selection of one canonical E-occupancy sort and its TRUE equivariant
retyping, with Arrow-action compatibility, are separate next steps.
-/

universe u v w t

namespace CCO.ExactEPGeometry

open APCharacter.Towers
open RigidGroupoid.Geometry

noncomputable section

/-- A genuine old current K-gate class corresponds bijectively to
an actual projected K/E class in the already constructed C67
ALL-parent source. The K/E relation is FULL RAW exact by the real
C82 source theorem, not by a hypothetical quotient exactness input. -/
noncomputable def originalAllparentGateClassEquiv
    (A B : CurrentSource.{u,v,w,t})
    (P : UnaryReduct A.source B.source)
    (transport : ExactTraceTransport A.source B.source P)
    (tp : ExactTraceProduct A.source B.source P)
    (base : A.Sorts) (hOne : ∀ i : A.Sorts, base = i)
    (E : ExactEq A.source base)
    (p : B.Sorts) (K : Kernel B.source p)
    (hNested : originalExactOnCurrentSort A B P transport
      base hOne E p ≤ current_kernel_exact_eq B K) :
    K.Class ≃
      (originalCoherentAllparentProjectedKernel
        A B P transport tp base hOne E p K hNested).Class := by
  let Q := originalExactAllCurrentQuotientCurrentSource
    A B P transport base hOne E
  let pi : B.Point p → Q.Point p := fun x => Quotient.mk'' x
  have hNestedPi : ∀ x y, pi x = pi y → K.rel x y := by
    intro x y hxy
    exact hNested (Quotient.exact hxy)
  change K.Class ≃ Quotient
    (K.projectedSetoid pi Quotient.mk''_surjective hNestedPi)
  exact projectedGateClassEquiv K pi Quotient.mk''_surjective hNestedPi

/-- C82 actual one-point class formula. Quotienting old points by
E and then by K/E gives the same class as quotienting directly by K. -/
theorem originalAllparentGateClassEquiv_mk
    (A B : CurrentSource.{u,v,w,t})
    (P : UnaryReduct A.source B.source)
    (transport : ExactTraceTransport A.source B.source P)
    (tp : ExactTraceProduct A.source B.source P)
    (base : A.Sorts) (hOne : ∀ i : A.Sorts, base = i)
    (E : ExactEq A.source base)
    (p : B.Sorts) (K : Kernel B.source p)
    (hNested : originalExactOnCurrentSort A B P transport
      base hOne E p ≤ current_kernel_exact_eq B K)
    (x : B.Point p) :
    originalAllparentGateClassEquiv
        A B P transport tp base hOne E p K hNested (K.project x) =
      (originalCoherentAllparentProjectedKernel
        A B P transport tp base hOne E p K hNested).project
          (Quotient.mk'' x) := by
  rfl

end
end CCO.ExactEPGeometry
