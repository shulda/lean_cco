import CCO.ExactEPGeometry.ExactTraceTransport
import CCO.ExactEPGeometry.ActualUnaryExactFromOld
import CCO.ExactEPGeometry.ActualUnaryExactTrace
import CCO.APCharacter.SourceAge.SingleStep

/-!
# B062 C28: real one-step exact transport for a canonical AP-only split

The generic two-way exact-trace interface is discharged for the ACTUAL
`SingleStep.successor`, using its constructed full-character phase, its
homogeneous marked age and its real old-reduct identification.

This is deliberately not a claim about arbitrary `CurrentSource.ActualStep`:
an arbitrary unary refinement need not preserve exactness in reverse.
-/

universe u v w t

namespace CCO.ExactEPGeometry

open APCharacter APCharacter.SourceAge APCharacter.Towers
open RigidGroupoid.Geometry

noncomputable section

/-- A genuine one-step C23–C27 application supplies BOTH directions of
full equality-inclusive represented RAW exactness, with nonempty old trace
as an explicit guard in the old-to-child direction. -/
theorem canonical_step_exact_transport
    (B : CurrentSource.{u,v,w,t})
    {i : B.Sorts} {K : Kernel B.source i}
    (P : SourcePhase B.source B.homogeneous
      (exactCalculus_of_homogeneous_CCO B.source B.homogeneous B.cco) K) :
    ExactTraceTransport B.source
      (SingleStep.successor B P).source (SingleStep.projection B P) := by
  let I := SingleStep.identification B P
  change ExactTraceTransport B.source
    (UnarySource.source I) (SourceAge.actualProjection I)
  constructor
  · intro c d D hOldTrace
    obtain ⟨x,z,hxz⟩ := hOldTrace
    have hInv : TRel.Invariant (G := B.G)
        (RawExact.evaluate B.source D.words) :=
      RawExact.presentation_invariant_of_homogeneous B.source
        B.homogeneous D.words
    have hMarked :
        ∃ a b : Age.Limit B.source B.homogeneous
            (P.completion_property B.cco),
          markedTrace B.source B.homogeneous
            (P.completion_property B.cco)
            (RawExact.evaluate B.source D.words)
            c.2.val d.2.val a b := by
      refine ⟨UnarySource.newEquiv I ⟨c,x⟩,
        UnarySource.newEquiv I ⟨d,z⟩,?_⟩
      exact (ActualUnaryTrace.real_child_trace_iff I
        (RawExact.evaluate B.source D.words) hInv x z).mpr hxz
    obtain ⟨E,hE⟩ :=
      ActualUnaryExactFromOld.original_exact_trace_has_current_exact
        P B.cco I D hMarked
    refine ⟨E,?_⟩
    intro y y'
    exact (hE y y').trans
      (ActualUnaryTrace.real_child_trace_iff I
        (RawExact.evaluate B.source D.words) hInv y y')
  · intro c d E
    obtain ⟨D,hD⟩ :=
      ActualUnaryExactTrace.current_exact_has_original_lift P B.cco I E
    have hInv : TRel.Invariant (G := B.G)
        (RawExact.evaluate B.source D.words) :=
      RawExact.presentation_invariant_of_homogeneous B.source
        B.homogeneous D.words
    refine ⟨D,?_⟩
    intro x z
    exact (hD x z).trans
      (ActualUnaryTrace.real_child_trace_iff I
        (RawExact.evaluate B.source D.words) hInv x z)

end
end CCO.ExactEPGeometry
