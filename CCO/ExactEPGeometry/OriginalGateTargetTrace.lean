import CCO.ExactEPGeometry.OriginalBridgeTrace

/-!
# B062 C55–C56: canonical ORIGINAL gate on the target of a full bridge

For a genuine current full exact Arrow R:p->q whose types come from
ONE original source sort, the proved original full saturated
correspondence C has literal p,q trace R and C²=G_p.

Actual original same-sort symmetry Cᵒᵖ=C gives its q,p trace Rᵒᵖ.
Two REAL nonempty input traces and the source displayed-middle (TP),
now with CURRENT middle sort p, identify G_p|q² with
Rᵒᵖ;R=K_q, the REAL target gate.

The original parent indices are related by an ACTUAL equality and
its two one-sided exact word transports. We do NOT eliminate the
equality by an invalid dependent case split on P.parent q.
No quotient SAP, group section or arbitrary mixed reverse descent.
-/

universe u v w t

namespace CCO.ExactEPGeometry

open APCharacter.Towers
open RigidGroupoid.Geometry

noncomputable section

variable {ι : Type u} {X : ι → Type v}

/-- Reindex the FIRST endpoint of a real original RAW exact presentation
along an ACTUAL equality of original source sorts; no new word or axiom. -/
def oldExactLeftCast
    (S : AtomicSource.{u,v,w} ι X) {i j : ι}
    (h : i = j) (D : RawExact.NonemptyExact S i i) :
    RawExact.NonemptyExact S j i := by
  cases h
  exact D

theorem oldExactLeftCast_iff
    (S : AtomicSource.{u,v,w} ι X) {i j : ι}
    (h : i = j) (D : RawExact.NonemptyExact S i i)
    (x : X j) (y : X i) :
    RawExact.evaluate S (oldExactLeftCast S h D).words x y ↔
      RawExact.evaluate S D.words (h.symm ▸ x) y := by
  cases h
  exact Iff.rfl

/-- The two reindexed REAL exact factors still have their middle
witness in the ORIGINAL i sort. This is an equality transport of
represented RAW composition, not a quotient-action identity. -/
theorem oldExactTwoSidedComp_iff
    (S : AtomicSource.{u,v,w} ι X) {i j : ι}
    (h : i = j) (D : RawExact.NonemptyExact S i i)
    (x y : X j) :
    TRel.comp
      (RawExact.evaluate S (oldExactLeftCast S h D).words)
      (RawExact.evaluate S (oldExactRightCast S h D).words) x y ↔
    TRel.comp (RawExact.evaluate S D.words)
      (RawExact.evaluate S D.words)
      (h.symm ▸ x) (h.symm ▸ y) := by
  cases h
  exact Iff.rfl

/-- The canonical largest ORIGINAL full exact gate G_p of a real
current bridge p->q has exactly current K_q as its q,q trace. The
equality hSame identifies only the two ORIGINAL source sort names,
not the genuinely distinct current unary types. -/
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
  dsimp only
  obtain ⟨C,hC⟩ :=
    current_arrow_original_correspondence_trace
      A B P transport tp hSame Kp Kq R
  let K := original_largest_gate_kernel A B P transport tp p Kp
  obtain ⟨Q,hQ⟩ := C.exact
  let Qqp : RawExact.NonemptyExact A.source
      (P.parent q) (P.parent p) :=
    oldExactLeftCast A.source hSame Q
  let Qpq : RawExact.NonemptyExact A.source
      (P.parent p) (P.parent q) :=
    oldExactRightCast A.source hSame Q
  have hQqp (y : B.Point q) (x : B.Point p) :
      RawExact.evaluate A.source Qqp.words
        (P.point q y) (P.point p x) ↔
      C.rel (hSame.symm ▸ P.point q y) (P.point p x) := by
    exact (oldExactLeftCast_iff A.source hSame Q
      (P.point q y) (P.point p x)).trans
        (Iff.of_eq (congrFun
          (congrFun hQ (hSame.symm ▸ P.point q y)) (P.point p x)))
  have hQpq (x : B.Point p) (y : B.Point q) :
      RawExact.evaluate A.source Qpq.words
        (P.point p x) (P.point q y) ↔
      C.rel (P.point p x) (hSame.symm ▸ P.point q y) := by
    exact (oldExactRightCast_iff A.source hSame Q
      (P.point p x) (P.point q y)).trans
        (Iff.of_eq (congrFun
          (congrFun hQ (P.point p x)) (hSame.symm ▸ P.point q y)))
  have hSym : TRel.converse C.rel = C.rel :=
    C.exact.same_sort_converse A.source A.homogeneous
  have hReverse (y : B.Point q) (x : B.Point p) :
      C.rel (hSame.symm ▸ P.point q y) (P.point p x) ↔
        R.rel x y := by
    have heq :
        C.rel (hSame.symm ▸ P.point q y) (P.point p x) =
          C.rel (P.point p x) (hSame.symm ▸ P.point q y) := by
      have hh := congrFun (congrFun hSym
        (hSame.symm ▸ P.point q y)) (P.point p x)
      exact hh.symm
    exact (Iff.of_eq heq).trans (hC x y)
  have hSquare : TRel.comp C.rel C.rel = K.rel := by
    calc
      TRel.comp C.rel C.rel =
          TRel.comp C.rel (TRel.converse C.rel) := by rw [hSym]
      _ = K.rel := C.source
  obtain ⟨x₀,y₀,hR₀⟩ := R.exact.nonempty B.source
  have hInputQP :
      ∃ y : B.Point q, ∃ x : B.Point p,
        RawExact.evaluate A.source Qqp.words
          (P.point q y) (P.point p x) := by
    refine ⟨y₀,x₀,?_⟩
    exact (hQqp y₀ x₀).mpr ((hReverse y₀ x₀).mpr hR₀)
  have hInputPQ :
      ∃ x : B.Point p, ∃ y : B.Point q,
        RawExact.evaluate A.source Qpq.words
          (P.point p x) (P.point q y) := by
    refine ⟨x₀,y₀,?_⟩
    exact (hQpq x₀ y₀).mpr ((hC x₀ y₀).mpr hR₀)
  intro y z
  have hTP := tp.product Qqp Qpq hInputQP hInputPQ y z
  have hCurrent :
      (∃ x : B.Point p,
        RawExact.evaluate A.source Qqp.words
          (P.point q y) (P.point p x) ∧
        RawExact.evaluate A.source Qpq.words
          (P.point p x) (P.point q z)) ↔
        TRel.comp (TRel.converse R.rel) R.rel y z := by
    constructor
    · rintro ⟨x,hYX,hXZ⟩
      exact ⟨x,(hReverse y x).mp ((hQqp y x).mp hYX),
        (hC x z).mp ((hQpq x z).mp hXZ)⟩
    · rintro ⟨x,hYX,hXZ⟩
      exact ⟨x,(hQqp y x).mpr ((hReverse y x).mpr hYX),
        (hQpq x z).mpr ((hC x z).mpr hXZ)⟩
  have hOld :
      TRel.comp (RawExact.evaluate A.source Qqp.words)
        (RawExact.evaluate A.source Qpq.words)
        (P.point q y) (P.point q z) ↔
      K.rel (hSame.symm ▸ P.point q y)
        (hSame.symm ▸ P.point q z) := by
    have hCast := oldExactTwoSidedComp_iff A.source hSame
      Q (P.point q y) (P.point q z)
    have hSource :
        TRel.comp (RawExact.evaluate A.source Q.words)
          (RawExact.evaluate A.source Q.words)
          (hSame.symm ▸ P.point q y)
          (hSame.symm ▸ P.point q z) ↔
        K.rel (hSame.symm ▸ P.point q y)
          (hSame.symm ▸ P.point q z) := by
      simpa only [hQ,hSquare]
    exact hCast.trans hSource
  have hGate :
      Kq.rel y z ↔ TRel.comp (TRel.converse R.rel) R.rel y z := by
    rw [R.target]
  exact hGate.trans (hCurrent.symm.trans (hTP.trans hOld))

end
end CCO.ExactEPGeometry
