import CCO.ExactEPGeometry.ExactTraceProduct
import CCO.ExactEPGeometry.CanonicalStepExact

/-!
# B062 C28: C22 exact trace-product at one ACTUAL canonical character step

The accepted original AP-only phase, its genuine marked limit and the
two-Peirce-choice C22 theorem supply (TP) for every pair of old nonempty RAW
exact domains with nonempty traces on the two specified child pairs.

The marked middle point furnished by C22 is decoded to THAT current child
using the proved whole-carrier identification. No anonymous middle sort,
quotient section, SAP or new binary identity colour enters the proof.
-/

universe u v w t

namespace CCO.ExactEPGeometry

open APCharacter APCharacter.SourceAge APCharacter.Towers
open RigidGroupoid.Geometry

noncomputable section

/-- Actual source-strength one-step (TP) on the genuine canonically
identified current point subtypes, for arbitrary equality-inclusive RAW
exact source factors and every genuinely nonempty choice of input traces. -/
theorem canonical_step_exact_product
    (B : CurrentSource.{u,v,w,t})
    {i : B.Sorts} {K : Kernel B.source i}
    (P : SourcePhase B.source B.homogeneous
      (exactCalculus_of_homogeneous_CCO B.source B.homogeneous B.cco) K) :
    ExactTraceProduct B.source
      (SourceAge.SingleStep.successor B P).source
      (SourceAge.SingleStep.projection B P) := by
  let I := SourceAge.SingleStep.identification B P
  change ExactTraceProduct B.source
    (UnarySource.source I) (SourceAge.actualProjection I)
  constructor
  intro c m d D E hD hE x z
  have hDInv : TRel.Invariant (G := B.G)
      (RawExact.evaluate B.source D.words) :=
    RawExact.presentation_invariant_of_homogeneous B.source
      B.homogeneous D.words
  have hEInv : TRel.Invariant (G := B.G)
      (RawExact.evaluate B.source E.words) :=
    RawExact.presentation_invariant_of_homogeneous B.source
      B.homogeneous E.words
  have hCompFull : FullExact B.source
      (TRel.comp (RawExact.evaluate B.source D.words)
        (RawExact.evaluate B.source E.words)) :=
    (exactCalculus_of_homogeneous_CCO
      B.source B.homogeneous B.cco).comp ⟨D,rfl⟩ ⟨E,rfl⟩
  have hCompInv : TRel.Invariant (G := B.G)
      (TRel.comp (RawExact.evaluate B.source D.words)
        (RawExact.evaluate B.source E.words)) :=
    hCompFull.invariant B.source B.homogeneous
  obtain ⟨a,b,hab⟩ := hD
  obtain ⟨b',c',hbc⟩ := hE
  have hInputD :
      ∃ a' b' : Age.Limit B.source B.homogeneous
          (P.completion_property B.cco),
        markedTrace B.source B.homogeneous
          (P.completion_property B.cco)
          (RawExact.evaluate B.source D.words)
          c.2.val m.2.val a' b' := by
    refine ⟨UnarySource.newEquiv I ⟨c,a⟩,
      UnarySource.newEquiv I ⟨m,b⟩,?_⟩
    exact (ActualUnaryTrace.real_child_trace_iff I
      (RawExact.evaluate B.source D.words) hDInv a b).mpr hab
  have hInputE :
      ∃ b' c' : Age.Limit B.source B.homogeneous
          (P.completion_property B.cco),
        markedTrace B.source B.homogeneous
          (P.completion_property B.cco)
          (RawExact.evaluate B.source E.words)
          m.2.val d.2.val b' c' := by
    refine ⟨UnarySource.newEquiv I ⟨m,b'⟩,
      UnarySource.newEquiv I ⟨d,c'⟩,?_⟩
    exact (ActualUnaryTrace.real_child_trace_iff I
      (RawExact.evaluate B.source E.words) hEInv b' c').mpr hbc
  have hTP := marked_trace_product
    B.source B.homogeneous P B.cco D E
      c.2.val m.2.val d.2.val
      hInputD hInputE
      (UnarySource.newEquiv I ⟨c,x⟩)
      (UnarySource.newEquiv I ⟨d,z⟩)
  constructor
  · rintro ⟨y,hxy,hyz⟩
    have hFirst :=
      (ActualUnaryTrace.real_child_trace_iff I
        (RawExact.evaluate B.source D.words) hDInv x y).mpr hxy
    have hSecond :=
      (ActualUnaryTrace.real_child_trace_iff I
        (RawExact.evaluate B.source E.words) hEInv y z).mpr hyz
    have hOutput := hTP.mp
      ⟨UnarySource.newEquiv I ⟨m,y⟩,hFirst,hSecond⟩
    exact (ActualUnaryTrace.real_child_trace_iff I
      (TRel.comp (RawExact.evaluate B.source D.words)
        (RawExact.evaluate B.source E.words))
      hCompInv x z).mp hOutput
  · intro hOutput
    have hMarkedOutput :=
      (ActualUnaryTrace.real_child_trace_iff I
        (TRel.comp (RawExact.evaluate B.source D.words)
          (RawExact.evaluate B.source E.words))
        hCompInv x z).mpr hOutput
    obtain ⟨q,hFirst,hSecond⟩ := hTP.mpr hMarkedOutput
    obtain ⟨y,hy⟩ :=
      ActualUnaryDecode.decode_child_of_bit I m q hFirst.2.1
    have hFirst' : markedTrace B.source B.homogeneous
        (P.completion_property B.cco)
        (RawExact.evaluate B.source D.words) c.2.val m.2.val
        (UnarySource.newEquiv I ⟨c,x⟩)
        (UnarySource.newEquiv I ⟨m,y⟩) := by
      rw [hy]
      exact hFirst
    have hSecond' : markedTrace B.source B.homogeneous
        (P.completion_property B.cco)
        (RawExact.evaluate B.source E.words) m.2.val d.2.val
        (UnarySource.newEquiv I ⟨m,y⟩)
        (UnarySource.newEquiv I ⟨d,z⟩) := by
      rw [hy]
      exact hSecond
    exact ⟨y,
      (ActualUnaryTrace.real_child_trace_iff I
        (RawExact.evaluate B.source D.words) hDInv x y).mp hFirst',
      (ActualUnaryTrace.real_child_trace_iff I
        (RawExact.evaluate B.source E.words) hEInv y z).mp hSecond'⟩

end
end CCO.ExactEPGeometry
