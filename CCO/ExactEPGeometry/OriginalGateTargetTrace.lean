import CCO.ExactEPGeometry.OriginalBridgeTrace

/-!
# B062 C55–C56: canonical ORIGINAL gate on the target of a full bridge

For a genuinely realized current full exact Arrow R:p->q whose types
come from ONE original source sort, the already proved original full
saturated correspondence C has literal p,q trace R and C² = G_p.

Original same-sort symmetry Cᵒᵖ=C gives its q,p trace Rᵒᵖ. Two
NONEMPTY real input traces and one application of the proved
displayed-middle TP (now with the CURRENT middle sort p) give
G_p|q² = Rᵒᵖ;R = K_q, the REAL target gate.

This proves the actual source C55–C56 gate-transport equation, not a
formal quotient-group action, source SAP, or a generic arbitrary
mixed-sort reverse exactness theorem.
-/

universe u v w t

namespace CCO.ExactEPGeometry

open APCharacter.Towers
open RigidGroupoid.Geometry

noncomputable section

/-- The canonical largest ORIGINAL full exact gate G_p of a real
current bridge p->q has exactly the CURRENT gate K_q as its
q,q-trace. The original-parent equality is explicit; the two
CURRENT sorts can still be genuinely distinct and both occupied. -/
theorem current_arrow_original_gate_target_trace
    (A B : CurrentSource.{u,v,w,t})
    (P : UnaryReduct A.source B.source)
    (transport : ExactTraceTransport A.source B.source P)
    (tp : ExactTraceProduct A.source B.source P)
    {p q : B.Sorts}
    (hSame : P.parent p = P.parent q)
    (Kp : Kernel B.source p) (Kq : Kernel B.source q)
    (R : Arrow B.source Kp Kq) :
    let K := original_largest_gate_kernel A B P transport tp p Kp
    ∀ y z : B.Point q,
      Kq.rel y z ↔
        K.rel (hSame.symm ▸ P.point q y)
          (hSame.symm ▸ P.point q z) := by
  cases hSame
  dsimp only
  obtain ⟨C,hC⟩ :=
    current_arrow_original_correspondence_trace
      A B P transport tp rfl Kp Kq R
  let K := original_largest_gate_kernel A B P transport tp p Kp
  obtain ⟨Q,hQ⟩ := C.exact
  have hSym : TRel.converse C.rel = C.rel :=
    C.exact.same_sort_converse A.source A.homogeneous
  have hReverse (y : B.Point q) (x : B.Point p) :
      C.rel (P.point q y) (P.point p x) ↔ R.rel x y := by
    have heq :
        C.rel (P.point q y) (P.point p x) =
          C.rel (P.point p x) (P.point q y) := by
      have h := congrFun (congrFun hSym (P.point q y)) (P.point p x)
      exact h.symm
    exact (Iff.of_eq heq).trans (hC x y)
  have hSquare : TRel.comp C.rel C.rel = K.rel := by
    calc
      TRel.comp C.rel C.rel =
          TRel.comp C.rel (TRel.converse C.rel) := by rw [hSym]
      _ = K.rel := C.source
  obtain ⟨x₀,y₀,hR₀⟩ := R.exact.nonempty B.source
  have hInputQP :
      ∃ y : B.Point q, ∃ x : B.Point p,
        RawExact.evaluate A.source Q.words
          (P.point q y) (P.point p x) := by
    refine ⟨y₀,x₀,?_⟩
    rw [hQ]
    exact (hReverse y₀ x₀).mpr hR₀
  have hInputPQ :
      ∃ x : B.Point p, ∃ y : B.Point q,
        RawExact.evaluate A.source Q.words
          (P.point p x) (P.point q y) := by
    refine ⟨x₀,y₀,?_⟩
    rw [hQ]
    exact (hC x₀ y₀).mpr hR₀
  intro y z
  have hTP := tp.product Q Q hInputQP hInputPQ y z
  have hCurrent :
      (∃ x : B.Point p,
        RawExact.evaluate A.source Q.words
          (P.point q y) (P.point p x) ∧
        RawExact.evaluate A.source Q.words
          (P.point p x) (P.point q z)) ↔
        TRel.comp (TRel.converse R.rel) R.rel y z := by
    constructor
    · rintro ⟨x,hYX,hXZ⟩
      have hC1 : C.rel (P.point q y) (P.point p x) := by
        rw [← hQ]
        exact hYX
      have hC2 : C.rel (P.point p x) (P.point q z) := by
        rw [← hQ]
        exact hXZ
      exact ⟨x,(hReverse y x).mp hC1,(hC x z).mp hC2⟩
    · rintro ⟨x,hYX,hXZ⟩
      refine ⟨x,?_,?_⟩
      · rw [hQ]
        exact (hReverse y x).mpr hYX
      · rw [hQ]
        exact (hC x z).mpr hXZ
  have hOld :
      TRel.comp (RawExact.evaluate A.source Q.words)
        (RawExact.evaluate A.source Q.words)
        (P.point q y) (P.point q z) ↔
      K.rel (P.point q y) (P.point q z) := by
    simpa only [hQ,hSquare]
  have hGate :
      Kq.rel y z ↔ TRel.comp (TRel.converse R.rel) R.rel y z := by
    rw [R.target]
  exact hGate.trans (hCurrent.symm.trans (hTP.trans hOld))

end
end CCO.ExactEPGeometry
