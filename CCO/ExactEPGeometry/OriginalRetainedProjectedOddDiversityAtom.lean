import CCO.ExactEPGeometry.OriginalRetainedAllparentOddOutsideGate
import CCO.APCharacter.SourcePhase

/-!
# B062 C97: one REAL diversity quotient atom outside the true projected gate

Start with an actual nonempty nonidentity odd Arrow of the source
maximal-character SourcePhase at a reached parent b. Its whole
relation avoids the current exact gate K_b by complete full-Arrow
uniqueness. The true original-E quotient has a fully exact projected
gate K_b/e_b whose literal pullback is K_b.

Choose a real old odd pair (x,y). Its two actual E-classes are
K_b/e_b-INEQUIVALENT, hence distinct as quotient points and have
a TRUE quotient diversity colour c. Homogeneity of the genuine
all-parent quotient source and invariance of its full gate show
that the ENTIRE quotient atomic orbital c is outside K_b/e_b.

The further C97 identity between the old atom's exact E-saturation
and this quotient orbital is governed by the established I10 orbital
pullback theorem and remains to be wired to the chosen old pivot.
C98–C105 remain separate. No SAP, group-action section or extra
source hypothesis.
-/

universe u v w t

namespace CCO.ExactEPGeometry

open APCharacter
open APCharacter.Towers
open RigidGroupoid.Geometry

noncomputable section

/-- A real old full odd Arrow projects to a GENUINE quotient
diversity ATOM, whose entire atomic relation avoids the actual
K_b/E_b full exact gate. No assumed quotient atom or fake logical
diagonal is introduced. -/
theorem originalRetainedAllparentOdd_hasQuotientDiversityAtom
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
    ∃ c : Q.source.Atom b.val b.val,
      (∃ p q : Q.Point b.val, Q.source.atomRel c p q) ∧
      ∀ p q : Q.Point b.val,
        Q.source.atomRel c p q → ¬ Kq.rel p q := by
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
  let odd := phase.atSort b
  have hOut : ∀ x y : B.Point b.val, odd.rel x y → ¬ K.rel x y := by
    intro x y hOdd hK
    have hSame : odd = Arrow.id K :=
      odd.eq_of_common_real_pair B.homogeneous (Arrow.id K) hOdd hK
    exact (phase.atSort_nonidentity b) hSame
  obtain ⟨x,y,hOdd⟩ := odd.exact.nonempty B.source
  let pi : B.Point b.val → Q.Point b.val := fun z => Quotient.mk'' z
  let qx : Q.Point b.val := pi x
  let qy : Q.Point b.val := pi y
  have hNoGate : ¬ Kq.rel qx qy := by
    intro hq
    have hPull := originalCoherentAllparentProjectedKernel_pullback
      A B P transport tp base hBase E b.val K hNested
    have hOld : K.rel x y :=
      (Iff.of_eq (congrFun (congrFun hPull x) y)).mp hq
    exact hOut x y hOdd hOld
  have hNE : qx ≠ qy := by
    intro heq
    exact hNoGate (heq ▸ Kq.setoid.refl qx)
  cases hc : Q.source.colour qx qy with
  | none =>
      have hTagged := (Q.source.colour_none_iff qx qy).mp hc
      have heq : qx = qy := by
        cases hTagged
        rfl
      exact False.elim (hNE heq)
  | some c =>
      have hAtom : Q.source.atomRel c qx qy := hc
      refine ⟨c,⟨qx,qy,hAtom⟩,?_⟩
      intro p q hPq hGate
      have hColour : Q.source.colour p q = Q.source.colour qx qy :=
        hPq.trans hc.symm
      obtain ⟨g,hgp,hgq⟩ :=
        (Q.source.pair_homogeneous_of_homogeneous Q.homogeneous)
          p qx q qy hColour
      have hGateMoved : Kq.rel qx qy := by
        simpa only [hgp,hgq] using
          Kq.exact.invariant Q.source Q.homogeneous g p q hGate
      exact hNoGate hGateMoved

end
end CCO.ExactEPGeometry
