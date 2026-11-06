import CCO.ExactEPGeometry.OriginalConnectedGate
import CCO.ExactEPGeometry.OriginalBridgeTrace

/-!
# B062 C57: original full-exact correspondences have REAL current exact traces

A genuine certified original-to-current unary reduct need not preserve
the exactness of EMPTY traces. The proved source transport does,
however, preserve EVERY nonempty old FULL RAW-exact restriction to
actual current endpoint types.

For an original exact relation on ONE original source sort, we
reindex only its second old endpoint along the ACTUAL original parent
equality, require a REAL current pair witness, and apply the already
proved ExactTraceTransport.old_to_new. The resulting CURRENT relation
is FULL exact in the actual current named binary language.

This is the exactness part of source C57/C58's CONVERSE bridge claim,
not yet the whole Arrow equations. No quotient SAP or imaginary group
section, no fake reverse descent of arbitrary mixed quotient relations.
-/

universe u v w t

namespace CCO.ExactEPGeometry

open APCharacter.Towers
open RigidGroupoid.Geometry

noncomputable section

/-- Nonempty actual unary trace of an ORIGINAL FULL-exact relation
on the shared original carrier is itself FULL RAW-exact in the
genuine current source. Each source instance is supplied by the
existing two-way canonical exact transport; the old-parent equality
only reindexes a genuine RAW exact word presentation. -/
theorem original_full_exact_nonempty_current_trace
    (A B : CurrentSource.{u,v,w,t})
    (P : UnaryReduct A.source B.source)
    (transport : ExactTraceTransport A.source B.source P)
    {p q : B.Sorts} (hSame : P.parent p = P.parent q)
    (R : TRel A.Point (P.parent p) (P.parent p))
    (hExact : FullExact A.source R)
    (hReal : ∃ x : B.Point p, ∃ y : B.Point q,
      R (P.point p x) (hSame.symm ▸ P.point q y)) :
    FullExact B.source
      (fun x : B.Point p => fun y : B.Point q =>
        R (P.point p x) (hSame.symm ▸ P.point q y)) := by
  obtain ⟨D,hD⟩ := hExact
  let Q : RawExact.NonemptyExact A.source
      (P.parent p) (P.parent q) :=
    oldExactRightCast A.source hSame D
  have hQ (x : B.Point p) (y : B.Point q) :
      RawExact.evaluate A.source Q.words
          (P.point p x) (P.point q y) ↔
        R (P.point p x) (hSame.symm ▸ P.point q y) := by
    exact (oldExactRightCast_iff A.source hSame D
      (P.point p x) (P.point q y)).trans
      (Iff.of_eq (congrFun
        (congrFun hD (P.point p x))
        (hSame.symm ▸ P.point q y)))
  have hQReal :
      ∃ x : B.Point p, ∃ y : B.Point q,
        RawExact.evaluate A.source Q.words
          (P.point p x) (P.point q y) := by
    obtain ⟨x,y,hxy⟩ := hReal
    exact ⟨x,y,(hQ x y).mpr hxy⟩
  obtain ⟨E,hE⟩ := transport.old_to_new Q hQReal
  refine ⟨E,?_⟩
  funext x y
  apply propext
  exact (hE x y).trans (hQ x y)

/-- Source C57 real exactness readout specialized to an ACTUAL original
full-exact quotient-functional correspondence Arrow. It does NOT
assume that the current trace is automatically an Arrow: the four
current gate equations still need genuine typed (TP) applications. -/
theorem original_arrow_nonempty_current_trace_exact
    (A B : CurrentSource.{u,v,w,t})
    (P : UnaryReduct A.source B.source)
    (transport : ExactTraceTransport A.source B.source P)
    {p q : B.Sorts} (hSame : P.parent p = P.parent q)
    (G : Kernel A.source (P.parent p))
    (C : Arrow A.source G G)
    (hReal : ∃ x : B.Point p, ∃ y : B.Point q,
      C.rel (P.point p x) (hSame.symm ▸ P.point q y)) :
    FullExact B.source
      (fun x : B.Point p => fun y : B.Point q =>
        C.rel (P.point p x) (hSame.symm ▸ P.point q y)) :=
  original_full_exact_nonempty_current_trace A B P transport
    hSame C.rel C.exact hReal

end
end CCO.ExactEPGeometry
