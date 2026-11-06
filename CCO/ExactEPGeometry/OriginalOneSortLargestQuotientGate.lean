import CCO.ExactEPGeometry.OriginalRetainedProjectedGateBase
import CCO.ExactEPGeometry.PrefixExactLargestLift
import CCO.ExactCRT.CanonicalTypedQuotients

/-!
# B062 C102: universal largest ORIGINAL E-quotient full-exact gate

Fix the genuine original one-sort source A, real current AP+HOM CCO
prefix B, and true exact-transport/TP reduct. For the current full-exact
gate K_p let G=L_p(K_p) be its canonical largest ORIGINAL exact lift.
When the chosen ORIGINAL E refines G, C70/C82 proves the real gate G/E
FULL RAW exact on the actual one-original-sort canonical E-quotient.

Take ANY OTHER full-exact quotient equivalence Z whose CURRENT p trace
is below K_p. The actual I10 full-exact pullback of Z is an ORIGINAL
full-exact equivalence H; its literal current trace is below K_p.
The genuine original largest-lift right adjunction therefore gives
H <= G, and quotient surjectivity implies Z <= G/E. No quotient SAP,
group-action section, unproved relation-section, or reverse arbitrary
mixed many-sort exactness is invoked.

The still separate C102 source obligation identifies the exact trace
of this original quotient gate on the ALREADY constructed selected
occupancy-indexed quotient prefix, and relates whole original gate
objects and full marked ages. This lemma proves the largest-fibre
universal order property without assuming that identification.
-/

universe u v w t

namespace CCO.ExactEPGeometry

open APCharacter.Towers
open RigidGroupoid.Geometry
open CCO.ParityHasse.Original

noncomputable section

/-- Full RAW exact original G/E exists, and is greater than EVERY
full RAW-exact original E-quotient equivalence Z whose true B-parent
trace is below the REAL current gate K. For an arbitrary Z the
trace condition is quantified universally; no assumed maximality of
Z or quotient SAP is used. -/
theorem originalOneSortLargestQuotientGate
    (A B : CurrentSource.{u,v,w,t})
    (P : UnaryReduct A.source B.source)
    (transport : ExactTraceTransport A.source B.source P)
    (tp : ExactTraceProduct A.source B.source P)
    (hOne : ∀ i j : A.Sorts, i = j)
    (p : B.Sorts) (K : Kernel B.source p)
    (E : ExactEq A.source (P.parent p))
    (hE : E ≤ PrefixExactLargestLift.largest A B P transport tp p
      (current_kernel_exact_eq B K)) :
    let base := P.parent p
    let hBase : ∀ i : A.Sorts, base = i := fun i => hOne base i
    let J := originalExactSourceKernelFamily A base hBase E
    let W := originalExactSourceKernelWords A base hBase E
    let hW := originalExactSourceKernelWords_relation A base hBase E
    let Q0 := CCO.ExactCRT.CanonicalTyped.source
      A.source A.homogeneous J W hW
    let pi : A.Point base → Quotient (J base) :=
      CCO.ExactCRT.CanonicalTyped.projection J base
    let G := PrefixExactLargestLift.largest A B P transport tp p
      (current_kernel_exact_eq B K)
    FullExact Q0 (CCO.ExactCRT.quotientRelation pi pi
      (fun x y : A.Point base => G x y)) ∧
    ∀ Z : Kernel Q0 base,
      (∀ x y : B.Point p,
        Z.rel (pi (P.point p x)) (pi (P.point p y)) →
          K.rel x y) →
      ∀ q s : Quotient (J base), Z.rel q s →
        CCO.ExactCRT.quotientRelation pi pi
          (fun x y : A.Point base => G x y) q s := by
  let base := P.parent p
  let hBase : ∀ i : A.Sorts, base = i := fun i => hOne base i
  let J := originalExactSourceKernelFamily A base hBase E
  let W := originalExactSourceKernelWords A base hBase E
  let hW := originalExactSourceKernelWords_relation A base hBase E
  let Q0 := CCO.ExactCRT.CanonicalTyped.source
    A.source A.homogeneous J W hW
  let pi : A.Point base → Quotient (J base) :=
    CCO.ExactCRT.CanonicalTyped.projection J base
  let G := PrefixExactLargestLift.largest A B P transport tp p
    (current_kernel_exact_eq B K)
  have hGate : FullExact Q0
      (CCO.ExactCRT.quotientRelation pi pi
        (fun x y : A.Point base => G x y)) :=
    original_retained_original_quotient_gate_exact
      A base hBase E G hE
  change FullExact Q0
    (CCO.ExactCRT.quotientRelation pi pi
      (fun x y : A.Point base => G x y)) ∧
    ∀ Z : Kernel Q0 base,
      (∀ x y : B.Point p,
        Z.rel (pi (P.point p x)) (pi (P.point p y)) →
          K.rel x y) →
      ∀ q s : Quotient (J base), Z.rel q s →
        CCO.ExactCRT.quotientRelation pi pi
          (fun x y : A.Point base => G x y) q s
  refine ⟨hGate,?_⟩
  intro Z hTrace q s hZ
  let Hrel : TRel A.Point base base :=
    GroupActions.pullback pi pi Z.rel
  obtain ⟨D,hD⟩ := Z.exact
  let F := CCO.ExactCRT.CanonicalTyped.exactPullback
    A.source A.homogeneous J W hW A.cco D
  have hFull : FullExact A.source Hrel := by
    refine ⟨F,?_⟩
    have hF := CCO.ExactCRT.CanonicalTyped.exactPullback_relation
      A.source A.homogeneous J W hW A.cco D
    exact hF.trans (congrArg (GroupActions.pullback pi pi) hD)
  let H : ExactEq A.source base :=
    ⟨⟨Setoid.comap pi Z.setoid,
      groupInvariant_colourInvariant A.source A.homogeneous
        (hFull.invariant A.source A.homogeneous)⟩,hFull⟩
  have hTraceH :
      PrefixExactRestriction.rho A B P transport p H ≤
        current_kernel_exact_eq B K := by
    intro x y hxy
    apply hTrace x y
    exact (PrefixExactRestriction.rho_iff A B P transport
      p H x y).mp hxy
  have hHG : H ≤ G :=
    ((PrefixExactLargestLift.largest_spec A B P transport tp
      p (current_kernel_exact_eq B K)).2 H).mp hTraceH
  obtain ⟨a,rfl⟩ := Quotient.mk''_surjective q
  obtain ⟨z,rfl⟩ := Quotient.mk''_surjective s
  have hG : G a z := hHG hZ
  exact ⟨a,z,rfl,rfl,hG⟩

end
end CCO.ExactEPGeometry
