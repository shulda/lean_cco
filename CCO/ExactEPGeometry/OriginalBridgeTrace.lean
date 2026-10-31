import CCO.ExactEPGeometry.OriginalCommonGateArrow

/-!
# B062 C55: ACTUAL trace of the ORIGINAL saturated gate correspondence

A current FULL exact Arrow R:p->q with the two current gate kernels
has a real original same-parent exact D. The preceding theorem has
constructed the ORIGINAL whole correspondence C = G_p;D under the
canonical largest full-exact old gate G_p.

Here we prove the missing source statement that its COMPLETE p,q trace
is exactly the ACTUAL current R. The proof invokes (TP) for G_p and D
with the middle point constrained to p; the two input traces have real
nonempty witnesses, the old gate trace is exactly current K_p via the
already proved E1/E2/E3 largest-fibre theorem, and the actual
current Arrow.left equation says K_p;R = R.

No arbitrary original group action section, pointwise function, quotient
SAP, unguarded product trace or missing old-parent identification.
-/

universe u v w t

namespace CCO.ExactEPGeometry

open APCharacter.Towers
open RigidGroupoid.Geometry

noncomputable section

/-- Source C55: the canonical ORIGINAL full exact saturated arrow
really traces to the ENTIRE current cross-type full bridge, rather
than merely containing it. The equality hSame concerns only the
ONE ORIGINAL source sort; the current types p and q need not agree. -/
theorem current_arrow_original_correspondence_trace
    (A B : CurrentSource.{u,v,w,t})
    (P : UnaryReduct A.source B.source)
    (transport : ExactTraceTransport A.source B.source P)
    (tp : ExactTraceProduct A.source B.source P)
    {p q : B.Sorts}
    (hSame : P.parent p = P.parent q)
    (Kp : Kernel B.source p) (Kq : Kernel B.source q)
    (R : Arrow B.source Kp Kq) :
    let K := original_largest_gate_kernel A B P transport tp p Kp
    ∃ C : Arrow A.source K K,
      ∀ x : B.Point p, ∀ y : B.Point q,
        C.rel (P.point p x) (hSame.symm ▸ P.point q y) ↔
          R.rel x y := by
  cases hSame
  dsimp only
  obtain ⟨E,C,hER,hC⟩ :=
    current_arrow_has_original_correspondence
      A B P transport tp rfl Kp Kq R
  let K := original_largest_gate_kernel A B P transport tp p Kp
  let F := current_kernel_exact_eq B Kp
  let G := PrefixExactLargestLift.largest A B P transport tp p F
  have hGLift :
      PrefixExactRestriction.rho A B P transport p G = F :=
    (PrefixExactLargestLift.largest_spec A B P transport tp p F).1
  have hGate (x z : B.Point p) :
      K.rel (P.point p x) (P.point p z) ↔ Kp.rel x z := by
    change G (P.point p x) (P.point p z) ↔ F x z
    have h := (PrefixExactRestriction.rho_iff
      A B P transport p G x z).symm
    rw [hGLift] at h
    exact h
  obtain ⟨Q,hQ⟩ := K.exact
  let a : B.Point p := Classical.choice (B.source.nonemptySort p)
  have hQIn :
      ∃ x : B.Point p, ∃ z : B.Point p,
        RawExact.evaluate A.source Q.words
          (P.point p x) (P.point p z) := by
    refine ⟨a,a,?_⟩
    rw [hQ]
    exact (hGate a a).mpr (Kp.setoid.refl a)
  obtain ⟨a₀,b₀,hab⟩ := R.exact.nonempty B.source
  have hEIn :
      ∃ x : B.Point p, ∃ y : B.Point q,
        RawExact.evaluate A.source E.words
          (P.point p x) (P.point q y) :=
    ⟨a₀,b₀,(hER a₀ b₀).mp hab⟩
  refine ⟨C,?_⟩
  intro x y
  have hTP := tp.product Q E hQIn hEIn x y
  have hCurrent :
      (∃ z : B.Point p,
        RawExact.evaluate A.source Q.words
          (P.point p x) (P.point p z) ∧
        RawExact.evaluate A.source E.words
          (P.point p z) (P.point q y)) ↔
        TRel.comp Kp.rel R.rel x y := by
    constructor
    · rintro ⟨z,hxz,hzy⟩
      have hK : K.rel (P.point p x) (P.point p z) := by
        rw [← hQ]
        exact hxz
      exact ⟨z,(hGate x z).mp hK,(hER z y).mpr hzy⟩
    · rintro ⟨z,hxz,hzy⟩
      refine ⟨z,?_,(hER z y).mp hzy⟩
      rw [hQ]
      exact (hGate x z).mpr hxz
  have hOld :
      C.rel (P.point p x) (P.point q y) ↔
        TRel.comp (RawExact.evaluate A.source Q.words)
          (RawExact.evaluate A.source E.words)
          (P.point p x) (P.point q y) := by
    simpa only [hC,hQ]
  have hLeft : TRel.comp Kp.rel R.rel x y ↔ R.rel x y := by
    rw [R.left]
  exact hOld.trans (hTP.symm.trans (hCurrent.trans hLeft))

end
end CCO.ExactEPGeometry
