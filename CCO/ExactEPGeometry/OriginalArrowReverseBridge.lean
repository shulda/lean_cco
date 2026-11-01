import CCO.ExactEPGeometry.OriginalArrowCurrentExact

/-!
# B062 C57–C58: reverse complete bridge transport with REAL current arrows

An ACTUAL original full RAW-exact quotient-gate Arrow C:G -> G has
a nonempty p,q trace, for two genuinely realized current unary types
with the SAME old parent sort. Suppose the ORIGINAL gate G restricts
EXACTLY to the actual current exact kernels Kp and Kq.

Then the current trace is a complete current Arrow Kp -> Kq:
full RAW exactness is proved by old_to_new exact transport;
all FOUR whole relational equations (left/right/source/target)
are derived from original Arrow laws and proved fixed-middle (TP).
Each TP input has an ACTUAL witness in its DISPLAYED current sort:
p or q, never just an old parent point. Both old equality casts are
explicit original-sort transports, not quotient actions or group sections.

The extra gate-trace equalities are the already PROVED canonical
E1/E2/E3 source-restriction and C56 target-trace results when G is
the common actual original maximal exact gate of the full step.
This is not a generic mixed original-sort converse theorem.
-/

universe u v w t

namespace CCO.ExactEPGeometry

open APCharacter.Towers
open RigidGroupoid.Geometry

noncomputable section

variable {ι : Type u} {X : ι → Type v}

/-- Reindex both endpoints of a genuine OLD exact presentation along a
literal equality of original sorts. The underlying RAW words and their
true nonempty witnesses are transported, never asserted in a quotient. -/
def oldExactBothCast
    (S : AtomicSource.{u,v,w} ι X) {i j : ι}
    (h : i = j) (D : RawExact.NonemptyExact S i i) :
    RawExact.NonemptyExact S j j := by
  cases h
  exact D

theorem oldExactBothCast_iff
    (S : AtomicSource.{u,v,w} ι X) {i j : ι}
    (h : i = j) (D : RawExact.NonemptyExact S i i)
    (y z : X j) :
    RawExact.evaluate S (oldExactBothCast S h D).words y z ↔
      RawExact.evaluate S D.words (h.symm ▸ y) (h.symm ▸ z) := by
  cases h
  exact Iff.rfl

/-- The first typed ORIGINAL current-bridge square (p,q);(q,p)
has intermediate actual OLD sort j, but is only an equality-cast of
the genuine old square C;C on the SAME original carrier. -/
theorem oldExactSourceSquareCast_iff
    (S : AtomicSource.{u,v,w} ι X) {i j : ι}
    (h : i = j) (D : RawExact.NonemptyExact S i i)
    (x z : X i) :
    TRel.comp
      (RawExact.evaluate S (oldExactRightCast S h D).words)
      (RawExact.evaluate S (oldExactLeftCast S h D).words) x z ↔
    TRel.comp (RawExact.evaluate S D.words)
      (RawExact.evaluate S D.words) x z := by
  cases h
  exact Iff.rfl

/-- Literal old parent-reindexing of the CURRENT right-saturation word
composition C;G, with middle sort j explicitly retained. -/
theorem oldExactRightSaturationCast_iff
    (S : AtomicSource.{u,v,w} ι X) {i j : ι}
    (h : i = j) (C G : RawExact.NonemptyExact S i i)
    (x : X i) (y : X j) :
    TRel.comp
      (RawExact.evaluate S (oldExactRightCast S h C).words)
      (RawExact.evaluate S (oldExactBothCast S h G).words) x y ↔
    TRel.comp (RawExact.evaluate S C.words)
      (RawExact.evaluate S G.words) x (h.symm ▸ y) := by
  cases h
  exact Iff.rfl

/-- The ACTUAL nonempty current p,q trace of a full ORIGINAL exact
G-quotient correspondence, with G|p²=Kp and G|q²=Kq, is a FULL current
RAW-exact Arrow Kp -> Kq. This proves all four source C57/C58 bridge
equations, not just the exactness or square identities. -/
noncomputable def original_arrow_trace_to_current_arrow
    (A B : CurrentSource.{u,v,w,t})
    (P : UnaryReduct A.source B.source)
    (transport : ExactTraceTransport A.source B.source P)
    (tp : ExactTraceProduct A.source B.source P)
    {p q : B.Sorts} (hSame : P.parent p = P.parent q)
    (G : Kernel A.source (P.parent p))
    (Kp : Kernel B.source p) (Kq : Kernel B.source q)
    (hGateP : ∀ x z : B.Point p,
      G.rel (P.point p x) (P.point p z) ↔ Kp.rel x z)
    (hGateQ : ∀ y z : B.Point q,
      G.rel (hSame.symm ▸ P.point q y)
        (hSame.symm ▸ P.point q z) ↔ Kq.rel y z)
    (C : Arrow A.source G G)
    (hReal : ∃ x : B.Point p, ∃ y : B.Point q,
      C.rel (P.point p x) (hSame.symm ▸ P.point q y)) :
    Arrow B.source Kp Kq := by
  let R : TRel B.Point p q :=
    fun x y => C.rel (P.point p x) (hSame.symm ▸ P.point q y)
  have hRExact : FullExact B.source R :=
    original_arrow_nonempty_current_trace_exact
      A B P transport hSame G C hReal
  obtain ⟨W,hW⟩ := C.exact
  obtain ⟨D,hD⟩ := G.exact
  let Wpq : RawExact.NonemptyExact A.source
      (P.parent p) (P.parent q) :=
    oldExactRightCast A.source hSame W
  let Wqp : RawExact.NonemptyExact A.source
      (P.parent q) (P.parent p) :=
    oldExactLeftCast A.source hSame W
  let Dqq : RawExact.NonemptyExact A.source
      (P.parent q) (P.parent q) :=
    oldExactBothCast A.source hSame D
  have hWpq (x : B.Point p) (y : B.Point q) :
      RawExact.evaluate A.source Wpq.words
        (P.point p x) (P.point q y) ↔ R x y := by
    exact (oldExactRightCast_iff A.source hSame W
      (P.point p x) (P.point q y)).trans
      (Iff.of_eq (congrFun (congrFun hW (P.point p x))
        (hSame.symm ▸ P.point q y)))
  have hWqp (y : B.Point q) (x : B.Point p) :
      RawExact.evaluate A.source Wqp.words
        (P.point q y) (P.point p x) ↔ R x y := by
    have hSym : TRel.converse C.rel = C.rel :=
      C.exact.same_sort_converse A.source A.homogeneous
    have hh : C.rel (hSame.symm ▸ P.point q y)
        (P.point p x) = C.rel (P.point p x)
          (hSame.symm ▸ P.point q y) := by
      have h := congrFun (congrFun hSym
        (hSame.symm ▸ P.point q y)) (P.point p x)
      exact h.symm
    exact (oldExactLeftCast_iff A.source hSame W
      (P.point q y) (P.point p x)).trans
      ((Iff.of_eq (congrFun (congrFun hW
        (hSame.symm ▸ P.point q y)) (P.point p x))).trans
        (Iff.of_eq hh))
  have hGpp (x z : B.Point p) :
      RawExact.evaluate A.source D.words
        (P.point p x) (P.point p z) ↔ Kp.rel x z :=
    (Iff.of_eq (congrFun (congrFun hD (P.point p x))
      (P.point p z))).trans (hGateP x z)
  have hGqq (y z : B.Point q) :
      RawExact.evaluate A.source Dqq.words
        (P.point q y) (P.point q z) ↔ Kq.rel y z :=
    (oldExactBothCast_iff A.source hSame D
      (P.point q y) (P.point q z)).trans
      ((Iff.of_eq (congrFun (congrFun hD
        (hSame.symm ▸ P.point q y))
        (hSame.symm ▸ P.point q z))).trans
        (hGateQ y z))
  obtain ⟨x₀,y₀,hxy₀⟩ := hReal
  have hInPQ : ∃ x : B.Point p, ∃ y : B.Point q,
      RawExact.evaluate A.source Wpq.words
        (P.point p x) (P.point q y) :=
    ⟨x₀,y₀,(hWpq x₀ y₀).mpr hxy₀⟩
  have hInQP : ∃ y : B.Point q, ∃ x : B.Point p,
      RawExact.evaluate A.source Wqp.words
        (P.point q y) (P.point p x) :=
    ⟨y₀,x₀,(hWqp y₀ x₀).mpr hxy₀⟩
  let a : B.Point p := Classical.choice (B.source.nonemptySort p)
  let b : B.Point q := Classical.choice (B.source.nonemptySort q)
  have hInGpp : ∃ x z : B.Point p,
      RawExact.evaluate A.source D.words
        (P.point p x) (P.point p z) :=
    ⟨a,a,(hGpp a a).mpr (Kp.setoid.refl a)⟩
  have hInGqq : ∃ y z : B.Point q,
      RawExact.evaluate A.source Dqq.words
        (P.point q y) (P.point q z) :=
    ⟨b,b,(hGqq b b).mpr (Kq.setoid.refl b)⟩
  have hSym : TRel.converse C.rel = C.rel :=
    C.exact.same_sort_converse A.source A.homogeneous
  have hSquare : TRel.comp C.rel C.rel = G.rel := by
    have hh := C.source
    rwa [hSym] at hh
  have hOldSquare (x z : A.Point (P.parent p)) :
      TRel.comp (RawExact.evaluate A.source W.words)
        (RawExact.evaluate A.source W.words) x z ↔ G.rel x z := by
    exact (Iff.of_eq (congrFun (congrFun
      (by simpa only [hW] using hSquare) x) z))
  have hLeftLaw (x z : A.Point (P.parent p)) :
      TRel.comp (RawExact.evaluate A.source D.words)
        (RawExact.evaluate A.source W.words) x z ↔ C.rel x z := by
    simpa only [hD,hW] using
      (Iff.of_eq (congrFun (congrFun C.left x) z))
  have hRightLaw (x z : A.Point (P.parent p)) :
      TRel.comp (RawExact.evaluate A.source W.words)
        (RawExact.evaluate A.source D.words) x z ↔ C.rel x z := by
    simpa only [hD,hW] using
      (Iff.of_eq (congrFun (congrFun C.right x) z))
  refine {
    rel := R
    exact := hRExact
    left := ?_
    right := ?_
    source := ?_
    target := ?_
  }
  · funext x y
    apply propext
    have hTP := tp.product D Wpq hInGpp hInPQ x y
    have hCur :
        (∃ z : B.Point p,
          RawExact.evaluate A.source D.words
            (P.point p x) (P.point p z) ∧
          RawExact.evaluate A.source Wpq.words
            (P.point p z) (P.point q y)) ↔
          TRel.comp Kp.rel R x y := by
      constructor
      · rintro ⟨z,hxz,hzy⟩
        exact ⟨z,(hGpp x z).mp hxz,(hWpq z y).mp hzy⟩
      · rintro ⟨z,hxz,hzy⟩
        exact ⟨z,(hGpp x z).mpr hxz,(hWpq z y).mpr hzy⟩
    have hOld :
        TRel.comp (RawExact.evaluate A.source D.words)
          (RawExact.evaluate A.source Wpq.words)
          (P.point p x) (P.point q y) ↔ R x y := by
      exact (oldExactRightCast_comp_iff A.source hSame
        (RawExact.evaluate A.source D.words) W
        (P.point p x) (P.point q y)).trans
        ((hLeftLaw _ _).trans Iff.rfl)
    exact (hCur.symm.trans (hTP.trans hOld))
  · funext x y
    apply propext
    have hTP := tp.product Wpq Dqq hInPQ hInGqq x y
    have hCur :
        (∃ z : B.Point q,
          RawExact.evaluate A.source Wpq.words
            (P.point p x) (P.point q z) ∧
          RawExact.evaluate A.source Dqq.words
            (P.point q z) (P.point q y)) ↔
          TRel.comp R Kq.rel x y := by
      constructor
      · rintro ⟨z,hxz,hzy⟩
        exact ⟨z,(hWpq x z).mp hxz,(hGqq z y).mp hzy⟩
      · rintro ⟨z,hxz,hzy⟩
        exact ⟨z,(hWpq x z).mpr hxz,(hGqq z y).mpr hzy⟩
    have hOld :
        TRel.comp (RawExact.evaluate A.source Wpq.words)
          (RawExact.evaluate A.source Dqq.words)
          (P.point p x) (P.point q y) ↔ R x y := by
      exact (oldExactRightSaturationCast_iff A.source hSame W D
        (P.point p x) (P.point q y)).trans
        ((hRightLaw _ _).trans Iff.rfl)
    exact (hCur.symm.trans (hTP.trans hOld))
  · funext x z
    apply propext
    have hTP := tp.product Wpq Wqp hInPQ hInQP x z
    have hCur :
        (∃ y : B.Point q,
          RawExact.evaluate A.source Wpq.words
            (P.point p x) (P.point q y) ∧
          RawExact.evaluate A.source Wqp.words
            (P.point q y) (P.point p z)) ↔
          TRel.comp R (TRel.converse R) x z := by
      constructor
      · rintro ⟨y,hxy,hyz⟩
        exact ⟨y,(hWpq x y).mp hxy,(hWqp y z).mp hyz⟩
      · rintro ⟨y,hxy,hyz⟩
        exact ⟨y,(hWpq x y).mpr hxy,(hWqp y z).mpr hyz⟩
    have hOld :
        TRel.comp (RawExact.evaluate A.source Wpq.words)
          (RawExact.evaluate A.source Wqp.words)
          (P.point p x) (P.point p z) ↔ Kp.rel x z := by
      exact (oldExactSourceSquareCast_iff A.source hSame W
        (P.point p x) (P.point p z)).trans
          ((hOldSquare _ _).trans (hGateP x z))
    exact (hCur.symm.trans (hTP.trans hOld))
  · funext y z
    apply propext
    have hTP := tp.product Wqp Wpq hInQP hInPQ y z
    have hCur :
        (∃ x : B.Point p,
          RawExact.evaluate A.source Wqp.words
            (P.point q y) (P.point p x) ∧
          RawExact.evaluate A.source Wpq.words
            (P.point p x) (P.point q z)) ↔
          TRel.comp (TRel.converse R) R y z := by
      constructor
      · rintro ⟨x,hyx,hxz⟩
        exact ⟨x,(hWqp y x).mp hyx,(hWpq x z).mp hxz⟩
      · rintro ⟨x,hyx,hxz⟩
        exact ⟨x,(hWqp y x).mpr hyx,(hWpq x z).mpr hxz⟩
    have hOld :
        TRel.comp (RawExact.evaluate A.source Wqp.words)
          (RawExact.evaluate A.source Wpq.words)
          (P.point q y) (P.point q z) ↔ Kq.rel y z := by
      exact (oldExactTwoSidedComp_iff A.source hSame W
        (P.point q y) (P.point q z)).trans
          ((hOldSquare _ _).trans (hGateQ y z))
    exact (hCur.symm.trans (hTP.trans hOld))

end
end CCO.ExactEPGeometry
