import CCO.ExactEPGeometry.QuotientParityProfiles

/-!
# B062 C98–C99: the SAME original odd atom yields complete quotient parity

On a reached actual source parent b, retain the SAME genuine SourcePhase
odd atom c and actual nonempty quotient diversity atom d whose complete
E-saturated image was proved in C97. The C98 exact all-length power
identity gives exact inverse-image formulas for the WHOLE even, odd and
connected profiles. In addition, the true phase character marking
excludes every odd c-walk from the whole old K, not merely old equality.
The real pullback of K/E and E<=K therefore forbid EVERY quotient odd
profile pair inside K/E. Genuine homogeneous source parity then provides
index two on the SAME d. This explicitly binds C97, C98 and C99 choices.

This does not yet identify the stabilized old even profile with e∨Y,
prove projected maximal full-exact gate, or construct the full quotient
marked age and safe tower. All source APIs and hypotheses are unchanged.
-/

universe u v w t

namespace CCO.ExactEPGeometry

open APCharacter
open APCharacter.Towers
open RigidGroupoid.Geometry
open CCO.ParityHasse.Original

noncomputable section

/-- The ONE actual c,d pair has all three complete parity/connected
profile inverse-image identities, whole projected-gate odd disjointness
and relative index two on every genuine quotient point. -/
theorem originalRetainedQuotientFullParityProfiles
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
    let e := originalExactCurrentKernelFamily
      A B P transport base hBase E b.val
    let K := Reached.kernel B.homogeneous
      (exactCalculus_of_homogeneous_CCO
        B.source B.homogeneous B.cco) b
    let Kq := originalCoherentAllparentProjectedKernel
      A B P transport tp base hBase E b.val K
        (original_retained_current_E_below_full_gate
          A B P transport tp hOne Kroot E hE b)
    ∃ (c : B.source.Atom b.val b.val)
      (d : Q.source.Atom b.val b.val),
      (∀ p q : Q.Point b.val,
        Q.source.atomRel d p q → ¬ Kq.rel p q) ∧
      (∀ p q : Q.Point b.val,
        OddWalk (Q.source.atomRel d) p q → ¬ Kq.rel p q) ∧
      (∀ p : Q.Point b.val,
        relativeIndex
          (evenColourEq Q.source Q.homogeneous d).val
          (connectivityColourEq Q.source Q.homogeneous d).val p = 2) ∧
      ∀ a z : B.Point b.val,
        (EvenWalk (Q.source.atomRel d)
            (Quotient.mk'' a : Q.Point b.val) (Quotient.mk'' z : Q.Point b.val) ↔
          setoidBiSaturation e (EvenWalk (B.source.atomRel c)) a z) ∧
        (OddWalk (Q.source.atomRel d)
            (Quotient.mk'' a : Q.Point b.val) (Quotient.mk'' z : Q.Point b.val) ↔
          setoidBiSaturation e (OddWalk (B.source.atomRel c)) a z) ∧
        (ConnectedWalk (Q.source.atomRel d)
            (Quotient.mk'' a : Q.Point b.val) (Quotient.mk'' z : Q.Point b.val) ↔
          setoidBiSaturation e (ConnectedWalk (B.source.atomRel c)) a z) := by
  let base := P.parent r
  let hBase : ∀ i : A.Sorts, base = i := fun i => hOne base i
  let Q := originalExactAllCurrentQuotientCurrentSource
    A B P transport base hBase E
  let e := originalExactCurrentKernelFamily
    A B P transport base hBase E b.val
  let K := Reached.kernel B.homogeneous
    (exactCalculus_of_homogeneous_CCO
      B.source B.homogeneous B.cco) b
  let hNested := original_retained_current_E_below_full_gate
    A B P transport tp hOne Kroot E hE b
  let Kq := originalCoherentAllparentProjectedKernel
    A B P transport tp base hBase E b.val K hNested
  let pi : B.Point b.val → Q.Point b.val := fun a => Quotient.mk'' a
  obtain ⟨c,d,_hOldNonempty,hContained,hOutside,hPowers⟩ :=
    originalRetainedOddQuotientPowers
      A B P transport tp hOne Kroot phase E hE b
  have hOldGatePull := originalCoherentAllparentProjectedKernel_pullback
    A B P transport tp base hBase E b.val K hNested
  have hOddOutside : ∀ p q : Q.Point b.val,
      OddWalk (Q.source.atomRel d) p q → ¬ Kq.rel p q := by
    intro p q hOdd hGate
    obtain ⟨a,ha⟩ := Quotient.mk''_surjective p
    obtain ⟨z,hz⟩ := Quotient.mk''_surjective q
    have hOddAZ : OddWalk (Q.source.atomRel d) (pi a) (pi z) := by
      simpa only [ha,hz] using hOdd
    obtain ⟨n,hn,hPath⟩ := hOddAZ
    obtain ⟨u,v,hau,hUV,hvz⟩ := (hPowers n a z).mp hPath
    have hKAZ : K.rel a z := by
      apply (Iff.of_eq (congrFun (congrFun hOldGatePull a) z)).mp
      simpa only [ha,hz] using hGate
    have hKUA : K.rel u a := hNested (e.symm hau)
    have hKZV : K.rel z v := hNested (e.symm hvz)
    have hKUV : K.rel u v := K.setoid.trans hKUA
      (K.setoid.trans hKAZ hKZV)
    exact (originalPhaseOddAtom_oddWalk_outsideGate
      B Kroot phase b c hContained n hn u v hUV) hKUV
  have hNoOdd : ∀ p : Q.Point b.val, ∀ n : Nat,
      Odd n → ¬ relPow (Q.source.atomRel d) n p p := by
    intro p n hn hPath
    exact hOddOutside p p ⟨n,hn,hPath⟩ (Kq.setoid.refl p)
  have hIndex : ∀ p : Q.Point b.val,
      relativeIndex
        (evenColourEq Q.source Q.homogeneous d).val
        (connectivityColourEq Q.source Q.homogeneous d).val p = 2 := by
    intro p
    exact parity_seed_index_two Q.source Q.homogeneous d hNoOdd p
  refine ⟨c,d,hOutside,hOddOutside,hIndex,?_⟩
  intro a z
  exact ⟨
    quotientEvenWalk_bisaturation_iff pi e
      (B.source.atomRel c) (Q.source.atomRel d) hPowers a z,
    quotientOddWalk_bisaturation_iff pi e
      (B.source.atomRel c) (Q.source.atomRel d) hPowers a z,
    quotientConnectedWalk_bisaturation_iff pi e
      (B.source.atomRel c) (Q.source.atomRel d) hPowers a z⟩

end
end CCO.ExactEPGeometry
