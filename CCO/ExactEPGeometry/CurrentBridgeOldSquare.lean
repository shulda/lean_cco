import CCO.ExactEPGeometry.OldGateStableEnvelope
import CCO.ExactEPGeometry.ExactTraceProduct

/-!
# B062 C51: old square of a GENUINE current exact bridge

For a real current full RAW-exact Arrow R:p->q, the proved two-way exact
trace transport supplies a REAL original nonempty RAW exact D with the
whole p,q current relation as its trace. Using the accepted RAW converse
presentation and both genuine nonempty child-pair witnesses, the actual
displayed-middle (TP) proves that D;Dᵒᵖ restricts to the ACTUAL gate K_p,
and Dᵒᵖ;D to the ACTUAL K_q.

The original middle sort is not silently identified with either current
middle sort; the TP witness is in the displayed q (respectively p).
The source's one-original-sort symmetry is a LATER, separately justified
step. No quotient SAP, group section, arbitrary word descent or new axiom.
-/

universe u v w t

namespace CCO.ExactEPGeometry

open APCharacter.Towers
open RigidGroupoid.Geometry

noncomputable section

/-- C51 source strength, with both ACTUAL endpoint gates and the
same old D. No assumed source-gate equation: both are proved from the
current Arrow source/target equalities and exact displayed-middle (TP). -/
theorem current_arrow_old_square_traces
    (A B : CurrentSource.{u,v,w,t})
    (P : UnaryReduct A.source B.source)
    (transport : ExactTraceTransport A.source B.source P)
    (tp : ExactTraceProduct A.source B.source P)
    {p q : B.Sorts}
    (Kp : Kernel B.source p) (Kq : Kernel B.source q)
    (R : Arrow B.source Kp Kq) :
    ∃ D : RawExact.NonemptyExact A.source (P.parent p) (P.parent q),
      (∀ x : B.Point p, ∀ y : B.Point q,
        R.rel x y ↔ RawExact.evaluate A.source D.words
          (P.point p x) (P.point q y)) ∧
      (∀ x z : B.Point p,
        Kp.rel x z ↔
          TRel.comp (RawExact.evaluate A.source D.words)
            (TRel.converse (RawExact.evaluate A.source D.words))
            (P.point p x) (P.point p z)) ∧
      (∀ y z : B.Point q,
        Kq.rel y z ↔
          TRel.comp (TRel.converse (RawExact.evaluate A.source D.words))
            (RawExact.evaluate A.source D.words)
            (P.point q y) (P.point q z)) := by
  obtain ⟨Q,hQ⟩ := R.exact
  obtain ⟨D,hD⟩ := transport.new_to_old Q
  have hBridge (x : B.Point p) (y : B.Point q) :
      R.rel x y ↔ RawExact.evaluate A.source D.words
        (P.point p x) (P.point q y) := by
    rw [← hQ]
    exact hD x y
  let E : RawExact.NonemptyExact A.source (P.parent q) (P.parent p) :=
    D.converse A.source
  have hE : RawExact.evaluate A.source E.words =
      TRel.converse (RawExact.evaluate A.source D.words) :=
    RawExact.evaluate_reverse A.source D.words
  obtain ⟨a,b,hab⟩ := R.exact.nonempty B.source
  have hInD :
      ∃ x : B.Point p, ∃ y : B.Point q,
        RawExact.evaluate A.source D.words (P.point p x) (P.point q y) :=
    ⟨a,b,(hBridge a b).mp hab⟩
  have hInE :
      ∃ y : B.Point q, ∃ x : B.Point p,
        RawExact.evaluate A.source E.words (P.point q y) (P.point p x) := by
    refine ⟨b,a,?_⟩
    rw [hE]
    exact (hBridge a b).mp hab
  refine ⟨D,hBridge,?_,?_⟩
  · intro x z
    have hTP := tp.product D E hInD hInE x z
    rw [hE] at hTP
    have hCurrent :
        (∃ y : B.Point q,
          RawExact.evaluate A.source D.words
            (P.point p x) (P.point q y) ∧
          TRel.converse (RawExact.evaluate A.source D.words)
            (P.point q y) (P.point p z)) ↔
          TRel.comp R.rel (TRel.converse R.rel) x z := by
      constructor
      · rintro ⟨y,hxy,hzy⟩
        exact ⟨y,(hBridge x y).mpr hxy,(hBridge z y).mpr hzy⟩
      · rintro ⟨y,hxy,hzy⟩
        exact ⟨y,(hBridge x y).mp hxy,(hBridge z y).mp hzy⟩
    have hGate :
        Kp.rel x z ↔ TRel.comp R.rel (TRel.converse R.rel) x z := by
      rw [R.source]
    exact hGate.trans (hCurrent.symm.trans hTP)
  · intro y z
    have hTP := tp.product E D hInE hInD y z
    rw [hE] at hTP
    have hCurrent :
        (∃ x : B.Point p,
          TRel.converse (RawExact.evaluate A.source D.words)
            (P.point q y) (P.point p x) ∧
          RawExact.evaluate A.source D.words
            (P.point p x) (P.point q z)) ↔
          TRel.comp (TRel.converse R.rel) R.rel y z := by
      constructor
      · rintro ⟨x,hyx,hxz⟩
        exact ⟨x,(hBridge x y).mpr hyx,(hBridge x z).mpr hxz⟩
      · rintro ⟨x,hyx,hxz⟩
        exact ⟨x,(hBridge x y).mp hyx,(hBridge x z).mp hxz⟩
    have hGate :
        Kq.rel y z ↔ TRel.comp (TRel.converse R.rel) R.rel y z := by
      rw [R.target]
    exact hGate.trans (hCurrent.symm.trans hTP)

end
end CCO.ExactEPGeometry
