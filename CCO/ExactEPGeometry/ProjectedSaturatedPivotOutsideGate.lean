import CCO.RigidGroupoid.Geometry.ProjectedKernels

/-!
# B062 C97: an E-saturated pivot outside the old full gate stays outside K/E

For genuine equivalences E ≤ K on a carrier, saturating any binary
relation R that is disjoint from K by E on both ends cannot introduce
a K-pair. Since the actual quotient projected full gate K/E pulls
back EXACTLY to K, the image of the E-saturated pivot remains disjoint
from the whole projected gate.

This is the complete equality-inclusive relation calculation
needed for the C97 claim that the quotient pivot remains diversity,
rather than becoming the logical quotient diagonal or the
(nontrivial) gate identity. It is valid for ALL pairs, including
original equality; it uses no SAP, quotient group-action section,
new exactness provider or arbitrary reverse RAW descent.

Actual C97 source consumers must still instantiate R with the
genuine source odd pivot, E with the original E restriction,
K with the same source-certified maximal gate, and retain the
precise quotient orbital and parity/index proofs. This lemma alone
is not the source C97–C105 safe-step construction.
-/

universe u v w q

namespace CCO.ExactEPGeometry

open RigidGroupoid.Geometry

noncomputable section

/-- If E is below the complete old gate K and R is disjoint from K,
every pair in E;R;E is still disjoint from K. In particular the
saturation cannot accidentally contain the actual diagonal. -/
theorem saturatedPivot_disjointGate
    {X : Type v} (E K : Setoid X) (hEK : E ≤ K)
    (R : X → X → Prop)
    (hOut : ∀ a b, R a b → ¬ K.r a b)
    {x y : X}
    (hSat : ∃ a b, E.r x a ∧ R a b ∧ E.r b y) :
    ¬ K.r x y := by
  intro hK
  obtain ⟨a,b,hxa,hab,hby⟩ := hSat
  have hax : K.r a x := hEK (E.symm hxa)
  have hyb : K.r y b := hEK (E.symm hby)
  have hkAB : K.r a b := K.trans hax (K.trans hK hyb)
  exact hOut a b hab hkAB

/-- On the ACTUAL projected K/E kernel, the image of the E-saturated
relation cannot meet the WHOLE gate identity. Only the true
K/E pullback and E≤K are used. This does not presume that the
projected relation is itself RAW exact; that is a separate C97
source obligation. -/
theorem projectedSaturatedPivot_disjointGate
    {ι : Type u} {X : ι → Type v} {Q : ι → Type q}
    {S : AtomicSource.{u,v,w} ι X}
    {i : ι} (K : Kernel S i)
    (E : Setoid (X i)) (hEK : E ≤ K.setoid)
    (pi : X i → Q i) (surj : Function.Surjective pi)
    (hNested : ∀ x y, pi x = pi y → K.rel x y)
    (R : X i → X i → Prop)
    (hOut : ∀ a b, R a b → ¬ K.rel a b)
    {p q : Q i}
    (hImage : Quotient.image pi pi
      (fun x y => ∃ a b, E.r x a ∧ R a b ∧ E.r b y) p q) :
    ¬ (K.projectedSetoid pi surj hNested).r p q := by
  intro hGate
  obtain ⟨x,y,hxp,hyq,hSat⟩ := hImage
  have hQ : (K.projectedSetoid pi surj hNested).r
      (pi x) (pi y) := by
    simpa only [hxp,hyq] using hGate
  have hPull := congrFun (congrFun
    (K.projected_pullback pi surj hNested) x) y
  have hK : K.rel x y := (Iff.of_eq hPull).mp hQ
  exact saturatedPivot_disjointGate E K.setoid hEK R hOut hSat hK

end
end CCO.ExactEPGeometry
