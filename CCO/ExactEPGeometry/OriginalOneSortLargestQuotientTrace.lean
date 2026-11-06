import CCO.ExactEPGeometry.OriginalOneSortLargestQuotientGate
import CCO.ExactCRT.Descent

/-!
# B062 C102: exact TRUE current trace of the largest original quotient gate

The canonical ORIGINAL full-exact gate G=L_p(K) is E-bisaturated when
the genuine retained E refines it. Its E-quotient G/E has a full
RAW-exact representation by C70/C82 and already has the universal
largest-lift property by OriginalOneSortLargestQuotientGate.

Here we additionally show that the literal pullback of G/E on the
ACTUAL original current parent p equals the full gate K, without
assuming a quotient trace lemma or identifying logical quotient Id
with the nontrivial K/E groupoid gate. The proof is the genuine
E-bisaturation equality followed by the actual source restriction
rho_p(G)=K. No quotient SAP, group section or future quotient phase.
-/

universe u v w t

namespace CCO.ExactEPGeometry

open APCharacter.Towers
open RigidGroupoid.Geometry

noncomputable section

/-- C102 exact trace: the full ORIGINAL E-quotient image of the
canonical ORIGINAL gate G has precisely K on the REAL current
parent p. The projected endpoints are true original E-classes. -/
theorem originalOneSortLargestQuotientGate_trace
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
    let pi : A.Point base → Quotient (J base) :=
      CCO.ExactCRT.CanonicalTyped.projection J base
    let G := PrefixExactLargestLift.largest A B P transport tp p
      (current_kernel_exact_eq B K)
    ∀ x y : B.Point p,
      CCO.ExactCRT.quotientRelation pi pi
        (fun a z : A.Point base => G a z)
        (pi (P.point p x)) (pi (P.point p y)) ↔ K.rel x y := by
  let base := P.parent p
  let hBase : ∀ i : A.Sorts, base = i := fun i => hOne base i
  let J := originalExactSourceKernelFamily A base hBase E
  let W := originalExactSourceKernelWords A base hBase E
  let hW := originalExactSourceKernelWords_relation A base hBase E
  let pi : A.Point base → Quotient (J base) :=
    CCO.ExactCRT.CanonicalTyped.projection J base
  let G := PrefixExactLargestLift.largest A B P transport tp p
    (current_kernel_exact_eq B K)
  have hKer : GroupActions.kernel pi =
      RawExact.evaluate A.source (W base).words :=
    CCO.ExactCRT.CanonicalTyped.projection_kernel
      A.source J W hW base
  have hSat : RawExact.saturate
      (RawExact.evaluate A.source (W base).words)
      (fun a z : A.Point base => G a z)
      (RawExact.evaluate A.source (W base).words) =
        (fun a z : A.Point base => G a z) :=
    original_retained_gate_E_saturated A base hBase E G hE
  have hPull := CCO.ExactCRT.pullback_quotientRelation
    pi pi (fun a z : A.Point base => G a z)
  rw [hKer] at hPull
  have hOld : GroupActions.pullback pi pi
      (CCO.ExactCRT.quotientRelation pi pi
        (fun a z : A.Point base => G a z)) =
      (fun a z : A.Point base => G a z) := hPull.trans hSat
  have hRho : PrefixExactRestriction.rho A B P transport p G =
      current_kernel_exact_eq B K :=
    (PrefixExactLargestLift.largest_spec A B P transport tp p
      (current_kernel_exact_eq B K)).1
  change ∀ x y : B.Point p,
    CCO.ExactCRT.quotientRelation pi pi
      (fun a z : A.Point base => G a z)
      (pi (P.point p x)) (pi (P.point p y)) ↔ K.rel x y
  intro x y
  have hPair := Iff.of_eq (congrFun (congrFun hOld
    (P.point p x)) (P.point p y))
  have hRhoPair := PrefixExactRestriction.rho_iff
    A B P transport p G x y
  rw [hRho] at hRhoPair
  exact hPair.trans hRhoPair.symm

/-- Combined real one-sort source C102: canonical ORIGINAL G/E is
FULL RAW exact, has the PRECISE current K trace, and dominates
EVERY original E-quotient full-exact equivalence whose actual current
trace is below K. This still does not claim selected occupancy
retyping or completion of the full marked quotient tower. -/
theorem originalOneSortLargestQuotientGate_complete
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
      (fun a z : A.Point base => G a z)) ∧
    (∀ x y : B.Point p,
      CCO.ExactCRT.quotientRelation pi pi
        (fun a z : A.Point base => G a z)
        (pi (P.point p x)) (pi (P.point p y)) ↔ K.rel x y) ∧
    ∀ Z : Kernel Q0 base,
      (∀ x y : B.Point p,
        Z.rel (pi (P.point p x)) (pi (P.point p y)) →
          K.rel x y) →
      ∀ q s : Quotient (J base), Z.rel q s →
        CCO.ExactCRT.quotientRelation pi pi
          (fun a z : A.Point base => G a z) q s := by
  dsimp only
  obtain ⟨hExact,hMax⟩ :=
    originalOneSortLargestQuotientGate
      A B P transport tp hOne p K E hE
  exact ⟨hExact,
    originalOneSortLargestQuotientGate_trace
      A B P transport tp hOne p K E hE,
    hMax⟩

end
end CCO.ExactEPGeometry
