import CCO.ExactEPGeometry.OriginalRetainedAllparentOddOutsideGate
import CCO.APCharacter.SourcePhase

/-!
# B062 C97: a genuine old diversity atomic pivot survives below full gate

The original reached SourcePhase carries an actual nonidentity
full-RAW-exact odd Arrow at every reached parent. Such an Arrow is
nonempty, and its full relation is disjoint from the corresponding
whole reached maximal gate. Select a REAL old atomic orbital inside
this odd Arrow, using the genuine old point pair and homogeneous
orbital invariance. Because that atom is contained in the odd
Arrow, it remains disjoint from the actual gate on ALL source pairs.

The actual original E≤G retained hypothesis then proves that
the two-sided E-saturation of this ONE atom, after projection to
the true all-parent quotient, cannot meet the full projected K/E
gate. Hence the image remains diversity; the quotient equality
pulls back to E and lies within K/E.

The quotient orbital naming provider (I10), selection of one
representative per original E-occupancy sort and parity/index-two
calculus remain separate C97–C99 source obligations.
-/

universe u v w t

namespace CCO.ExactEPGeometry

open APCharacter
open APCharacter.Towers
open RigidGroupoid.Geometry

noncomputable section

/-- Every TRUE reached odd SourcePhase Arrow contains a genuine
NONEMPTY old diversity orbital, disjoint from the entire full
reached gate K_b. Neither full-Arrow oddness nor gate identity
is reduced to a chosen generator or logical diagonal. -/
theorem originalReachedPhaseOdd_hasDiversAtomicPivot
    (B : CurrentSource.{u,v,w,t})
    {r : B.Sorts} (Kroot : Kernel B.source r)
    (phase : SourcePhase B.source B.homogeneous
      (exactCalculus_of_homogeneous_CCO
        B.source B.homogeneous B.cco) Kroot)
    (b : Reached B.source Kroot) :
    let K := Reached.kernel B.homogeneous
      (exactCalculus_of_homogeneous_CCO
        B.source B.homogeneous B.cco) b
    let odd := phase.atSort b
    ∃ c : B.source.Atom b.val b.val,
      (∃ x y : B.Point b.val, B.source.atomRel c x y) ∧
      ∀ x y : B.Point b.val,
        B.source.atomRel c x y →
          odd.rel x y ∧ ¬K.rel x y := by
  let C := exactCalculus_of_homogeneous_CCO
    B.source B.homogeneous B.cco
  let K := Reached.kernel B.homogeneous C b
  let odd := phase.atSort b
  have hOut : ∀ x y : B.Point b.val,
      odd.rel x y → ¬ K.rel x y := by
    intro x y hOdd hK
    have hEq : odd = Arrow.id K :=
      odd.eq_of_common_real_pair B.homogeneous (Arrow.id K) hOdd hK
    exact (phase.atSort_nonidentity b) hEq
  obtain ⟨x,y,hOdd⟩ := odd.exact.nonempty B.source
  have hDistinct : x ≠ y := by
    intro hxy
    subst y
    exact hOut x x hOdd (K.setoid.refl x)
  cases hc : B.source.colour x y with
  | none =>
      have hxy : x = y := by
        simpa only [Sigma.mk.injEq,heq_eq_eq,true_and] using
          (B.source.colour_none_iff x y).mp hc
      exact False.elim (hDistinct hxy)
  | some c =>
      have hAtom : B.source.atomRel c x y := hc
      refine ⟨c,⟨x,y,hAtom⟩,?_⟩
      intro a d hAd
      have hColour :
          B.source.colour x y = B.source.colour a d :=
        hc.trans hAd.symm
      obtain ⟨g,hgx,hgy⟩ :=
        (B.source.pair_homogeneous_of_homogeneous B.homogeneous)
          x a y d hColour
      have hOddAd : odd.rel a d := by
        simpa only [hgx,hgy] using
          odd.exact.invariant B.source B.homogeneous g x y hOdd
      exact ⟨hOddAd,hOut a d hOddAd⟩

/-- A TRUE source-proved old odd-diversity atom, with its REAL
old nonempty witness, has an E-saturated image outside the complete
projected K/E gate of the actual named all-parent quotient.
No pair is added to the gate by choosing E-class representatives. -/
theorem originalRetainedOddAtomicPivot_imageOutsideGate
    (A B : CurrentSource.{u,v,w,t})
    (P : UnaryReduct A.source B.source)
    (transport : ExactTraceTransport A.source B.source P)
    (tp : ExactTraceProduct A.source B.source P)
    (hOne : ∀ i j : A.Sorts, i = j)
    {r : B.Sorts} (Kroot : Kernel B.source r)
    (phase : SourcePhase B.source B.homogeneous
      (exactCalculus_of_homogeneous_CCO
        B.source B.homogeneous B.cco) Kroot)
    (E : ExactEq A.source (P.parent r))
    (hE : E ≤ PrefixExactLargestLift.largest A B P transport tp r
      (current_kernel_exact_eq B Kroot))
    (b : Reached B.source Kroot) :
    let base := P.parent r
    let hBase : ∀ i : A.Sorts, base = i := fun i => hOne base i
    let Q := originalExactAllCurrentQuotientCurrentSource
      A B P transport base hBase E
    let e := (originalExactOnCurrentSort
      A B P transport base hBase E b.val).val.val
    let K := Reached.kernel B.homogeneous
      (exactCalculus_of_homogeneous_CCO
        B.source B.homogeneous B.cco) b
    let Kq := originalCoherentAllparentProjectedKernel
      A B P transport tp base hBase E b.val K
        (original_retained_current_E_below_full_gate
          A B P transport tp hOne Kroot E hE b)
    ∃ c : B.source.Atom b.val b.val,
      (∃ x y : B.Point b.val, B.source.atomRel c x y) ∧
      ∀ p q : Q.Point b.val,
        Quotient.image
          (fun x : B.Point b.val => (Quotient.mk'' x : Q.Point b.val))
          (fun x : B.Point b.val => (Quotient.mk'' x : Q.Point b.val))
          (fun x y => ∃ a d, e.r x a ∧
            B.source.atomRel c a d ∧ e.r d y)
          p q → ¬ Kq.rel p q := by
  obtain ⟨c,hNonempty,hAtomOut⟩ :=
    originalReachedPhaseOdd_hasDiversAtomicPivot B Kroot phase b
  refine ⟨c,hNonempty,?_⟩
  intro p q hImage
  apply originalRetainedAllparentProjectedPivotOutsideGate
    A B P transport tp hOne Kroot E hE b
      (B.source.atomRel c) (fun x y h => (hAtomOut x y h).2)
  exact hImage

end
end CCO.ExactEPGeometry
