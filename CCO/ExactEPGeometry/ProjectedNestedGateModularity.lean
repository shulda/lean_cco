import CCO.RigidGroupoid.Geometry.ProjectedKernels

/-!
# B062 C100: modularity of E-saturation against a nested genuine full gate

For E ≤ K, intersecting the WHOLE gate K with the E-two-sided
saturation of an arbitrary relation X is literally the E-two-sided
saturation of K ∩ X. This is an equality of pointwise relations,
not only of RAW words and not only on diversity orbitals.

After projection by an actual surjective E-quotient map, the same
identity holds for the genuine projected gate K/E and images of the
E-saturated relations. The quotient identity pulls back to E,
whereas the *whole projected gate* pulls back to K.

Identifying E;X;E with e∨X under the relevant original commuting
equivalences is a separate actual source lemma, as is maximum-gate
complementation. This file assumes neither quotient SAP nor
arbitrary reverse RAW exactness or a group action section.
-/

universe u v w q

namespace CCO.ExactEPGeometry

open RigidGroupoid.Geometry

noncomputable section

/-- Full pointwise modularity, for ALL pairs including the original
diagonal: K∩(E;X;E) = E;(K∩X);E when E≤K. No commutation
hypothesis is needed for this two-sided saturation identity. -/
theorem nestedGate_inter_saturation_iff
    {X : Type v} (E K : Setoid X) (hEK : E ≤ K)
    (R : X → X → Prop) (x y : X) :
    (K.r x y ∧
      ∃ a b : X, E.r x a ∧ R a b ∧ E.r b y) ↔
    (∃ a b : X, E.r x a ∧ (K.r a b ∧ R a b) ∧ E.r b y) := by
  constructor
  · rintro ⟨hK, a, b, hxa, hab, hby⟩
    have hax : K.r a x := hEK (E.symm hxa)
    have hyb : K.r y b := hEK (E.symm hby)
    exact ⟨a,b,hxa,⟨K.trans hax (K.trans hK hyb),hab⟩,hby⟩
  · rintro ⟨a,b,hxa,⟨hKab,hab⟩,hby⟩
    have hKxa : K.r x a := hEK hxa
    have hKby : K.r b y := hEK hby
    exact ⟨K.trans hKxa (K.trans hKab hKby),⟨a,b,hxa,hab,hby⟩⟩

/-- After projection to the ACTUAL quotient, the whole K/E gate
intersected with a saturated original relation equals the
projected saturation of the original gate-intersection. This
does not claim the saturated relation is itself RAW exact. -/
theorem projectedNestedGate_inter_saturation_iff
    {ι : Type u} {X : ι → Type v} {Q : ι → Type q}
    {S : AtomicSource.{u,v,w} ι X}
    {i : ι} (K : Kernel S i)
    (E : Setoid (X i)) (hEK : E ≤ K.setoid)
    (pi : X i → Q i) (surj : Function.Surjective pi)
    (hNested : ∀ x y, pi x = pi y → K.rel x y)
    (R : X i → X i → Prop)
    (p q : Q i) :
    ((K.projectedSetoid pi surj hNested).r p q ∧
      Quotient.image pi pi
        (fun x y => ∃ a b, E.r x a ∧ R a b ∧ E.r b y) p q) ↔
    Quotient.image pi pi
      (fun x y => ∃ a b, E.r x a ∧
        (K.rel a b ∧ R a b) ∧ E.r b y) p q := by
  constructor
  · rintro ⟨hGate,⟨x,y,hxp,hyq,hSat⟩⟩
    have hQ : (K.projectedSetoid pi surj hNested).r
        (pi x) (pi y) := by
      simpa only [hxp,hyq] using hGate
    have hPb := congrFun (congrFun
      (K.projected_pullback pi surj hNested) x) y
    have hK : K.rel x y := (Iff.of_eq hPb).mp hQ
    exact ⟨x,y,hxp,hyq,
      (nestedGate_inter_saturation_iff E K.setoid hEK R x y).mp
        ⟨hK,hSat⟩⟩
  · rintro ⟨x,y,hxp,hyq,hSat⟩
    have hPair :=
      (nestedGate_inter_saturation_iff E K.setoid hEK R x y).mpr hSat
    have hPb := congrFun (congrFun
      (K.projected_pullback pi surj hNested) x) y
    have hQ : (K.projectedSetoid pi surj hNested).r
        (pi x) (pi y) := (Iff.of_eq hPb).mpr hPair.1
    constructor
    · simpa only [hxp,hyq] using hQ
    · exact ⟨x,y,hxp,hyq,hPair.2⟩

end
end CCO.ExactEPGeometry
