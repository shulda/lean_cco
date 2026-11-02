import CCO.ExactEPGeometry.OriginalRetainedOddAtomicPivot
import CCO.ExactEPGeometry.OriginalAllCurrentAtomicBlockImage

/-!
# B062 C97: the actual retained odd old orbital is ONE quotient diversity atom

Take the genuine old diversity atomic pair from the reached full
SourcePhase odd Arrow; it is disjoint from the entire reached gate.
The actual I10 E-block image theorem identifies its complete two-sided
E-saturation with precisely one orbit of the genuine all-parent quotient.
Since the real projected gate pulls back to the full old gate, that quotient
orbital cannot be equality, and ALL its pairs avoid the projected gate.

This combines the actual old odd pivot with the real quotient orbital
partition, rather than assuming that an arbitrary image stays atomic.
No quotient SAP, automorphism-group section, or mixed reverse descent.
The separate parity/index-two and projected maximality claims C98–C102
remain open.
-/

universe u v w t

namespace CCO.ExactEPGeometry

open APCharacter
open APCharacter.Towers
open RigidGroupoid.Geometry

noncomputable section

/-- The true source odd Arrow contains one real diversity atom c,
whose ENTIRE E-saturated block images onto one actual quotient atom d.
The complete relation of d is disjoint from the genuine full K/E gate,
so d is not quotient equality. -/
theorem originalRetainedOddAtomicBlock_imageQuotientDiversity
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
    let K := Reached.kernel B.homogeneous
      (exactCalculus_of_homogeneous_CCO
        B.source B.homogeneous B.cco) b
    let Kq := originalCoherentAllparentProjectedKernel
      A B P transport tp base hBase E b.val K
        (original_retained_current_E_below_full_gate
          A B P transport tp hOne Kroot E hE b)
    ∃ (c : B.source.Atom b.val b.val)
      (d : Q.source.Atom b.val b.val),
      (∃ x y : B.Point b.val, B.source.atomRel c x y) ∧
      (∀ x y : B.Point b.val,
        B.source.atomRel c x y → ¬ K.rel x y) ∧
      (∃ p q : Q.Point b.val, Q.source.atomRel d p q) ∧
      (∀ p q : Q.Point b.val,
        Quotient.image
          (fun z : B.Point b.val => (Quotient.mk'' z : Q.Point b.val))
          (fun z : B.Point b.val => (Quotient.mk'' z : Q.Point b.val))
          (Quotient.block B.source
            (originalExactCurrentKernelWords
              A B P transport base hBase E) (some c)) p q ↔
          Q.source.atomRel d p q) ∧
      (∀ p q : Q.Point b.val,
        Q.source.atomRel d p q → ¬ Kq.rel p q) := by
  let base := P.parent r
  let hBase : ∀ i : A.Sorts, base = i := fun i => hOne base i
  let Q := originalExactAllCurrentQuotientCurrentSource
    A B P transport base hBase E
  let K := Reached.kernel B.homogeneous
    (exactCalculus_of_homogeneous_CCO
      B.source B.homogeneous B.cco) b
  let hNested := original_retained_current_E_below_full_gate
    A B P transport tp hOne Kroot E hE b
  let Kq := originalCoherentAllparentProjectedKernel
    A B P transport tp base hBase E b.val K hNested
  obtain ⟨c,⟨x,y,hAtom⟩,hAtomOut⟩ :=
    originalReachedPhaseOdd_hasDiversAtomicPivot B Kroot phase b
  let qx : Q.Point b.val := Quotient.mk'' x
  let qy : Q.Point b.val := Quotient.mk'' y
  have hNoGate : ¬ Kq.rel qx qy := by
    intro hGate
    have hPull := originalCoherentAllparentProjectedKernel_pullback
      A B P transport tp base hBase E b.val K hNested
    have hOld : K.rel x y :=
      (Iff.of_eq (congrFun (congrFun hPull x) y)).mp hGate
    exact (hAtomOut x y hAtom).2 hOld
  have hNE : qx ≠ qy := by
    intro heq
    exact hNoGate (heq ▸ Kq.setoid.refl qx)
  cases hc : Q.source.colour qx qy with
  | none =>
      have hTagged := (Q.source.colour_none_iff qx qy).mp hc
      have hTyped : (⟨b.val,qx⟩ : Sigma Q.Point) =
          (⟨b.val,qy⟩ : Sigma Q.Point) := hTagged
      have heq : qx = qy := by
        have hh : HEq qx qy := ((Sigma.mk.inj_iff).mp hTyped).2
        exact eq_of_heq hh
      exact False.elim (hNE heq)
  | some d =>
      have hD : Q.source.atomRel d qx qy := hc
      refine ⟨c,d,⟨x,y,hAtom⟩,
        (fun a z ha => (hAtomOut a z ha).2),⟨qx,qy,hD⟩,?_,?_⟩
      · intro p q
        have hBlock := originalExactAllCurrentPairBlock_image
          A B P transport base hBase E x y p q
        have hOldColour : B.source.colour x y = some c := hAtom
        have hQuotColour :
            Q.source.colour (Quotient.mk'' x : Q.Point b.val)
              (Quotient.mk'' y : Q.Point b.val) = some d := hc
        simpa only [hOldColour,hQuotColour] using hBlock
      · intro p q hAtomPQ hGate
        have hColour : Q.source.colour p q = Q.source.colour qx qy :=
          hAtomPQ.trans hc.symm
        obtain ⟨g,hgp,hgq⟩ :=
          (Q.source.pair_homogeneous_of_homogeneous Q.homogeneous)
            p qx q qy hColour
        have hMoved : Kq.rel qx qy := by
          simpa only [hgp,hgq] using
            Kq.exact.invariant Q.source Q.homogeneous g p q hGate
        exact hNoGate hMoved

end
end CCO.ExactEPGeometry
