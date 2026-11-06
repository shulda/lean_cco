import CCO.ExactEPGeometry.OriginalAllCurrentQuotientSource
import CCO.ExactCRT.CanonicalTypedQuotients

/-!
# B062 C101: every REAL full exact quotient relation pulls back full exact

The all-parent E-quotient CurrentSource is literally the accepted
simultaneous exact quotient of the ACTUAL current B source by the true
original E restrictions on ALL parent sort names. Therefore the
accepted I10 canonical typed exactPullback theorem applies to EVERY
full RAW exact quotient relation, not just its fixed projected gate.

This source theorem is unconditional beyond the real standing
A/B/P/transport, one-original-sort E parameter and actual CCO.
No SAP, group-action section, arbitrary reverse quotient descent
or stronger old E nesting is supplied. The later strict-complement
maximality proof uses this for a candidate Kq' > Kq.
-/

universe u v w t

namespace CCO.ExactEPGeometry

open APCharacter.Towers
open RigidGroupoid.Geometry

noncomputable section

/-- Actual C101 reverse FULL-exact pullback on the genuine all-parent
E-quotient of the already constructed current AP+HOM CCO prefix.
The inverse image of any nonempty exact quotient relation has a
REAL old RAW nonempty exact presentation, with all equality included. -/
theorem originalExactAllCurrentFullExact_pullback
    (A B : CurrentSource.{u,v,w,t})
    (P : UnaryReduct A.source B.source)
    (transport : ExactTraceTransport A.source B.source P)
    (base : A.Sorts) (hOne : ∀ i : A.Sorts, base = i)
    (E : ExactEq A.source base)
    {p : B.Sorts}
    (D : (originalExactAllCurrentQuotientCurrentSource
      A B P transport base hOne E).Point p →
      (originalExactAllCurrentQuotientCurrentSource
        A B P transport base hOne E).Point p → Prop)
    (hExact : FullExact
      (originalExactAllCurrentQuotientCurrentSource
        A B P transport base hOne E).source D) :
    let Q := originalExactAllCurrentQuotientCurrentSource
      A B P transport base hOne E
    FullExact B.source
      (GroupActions.pullback
        (fun x : B.Point p => (Quotient.mk'' x : Q.Point p))
        (fun x : B.Point p => (Quotient.mk'' x : Q.Point p))
        D) := by
  let J := originalExactCurrentKernelFamily
    A B P transport base hOne E
  let W := originalExactCurrentKernelWords
    A B P transport base hOne E
  let hW := originalExactCurrentKernelWords_relation
    A B P transport base hOne E
  change FullExact
    (CCO.ExactCRT.CanonicalTyped.source B.source B.homogeneous J W hW)
    D at hExact
  obtain ⟨F,hF⟩ := hExact
  let oldF := CCO.ExactCRT.CanonicalTyped.exactPullback
    B.source B.homogeneous J W hW B.cco F
  refine ⟨oldF,?_⟩
  have hPull := CCO.ExactCRT.CanonicalTyped.exactPullback_relation
    B.source B.homogeneous J W hW B.cco F
  exact hPull.trans
    (congrArg (GroupActions.pullback
      (fun x : B.Point p => (Quotient.mk'' x : Quotient (J p)))
      (fun x : B.Point p => (Quotient.mk'' x : Quotient (J p)))) hF)

end
end CCO.ExactEPGeometry
