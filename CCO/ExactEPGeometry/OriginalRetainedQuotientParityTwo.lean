import CCO.ExactEPGeometry.OriginalPhaseOddWalkParity

/-!
# B062 C99: the real reached quotient odd pivot has index two

C97 chooses an actual old current atom c inside the genuine SourcePhase
odd Arrow, and a NONEMPTY genuine all-parent E-quotient diversity atom d,
whose whole relation avoids the full projected gate K/e. C98 proves for
this SAME c,d the equality of every quotient power and the literal
E-bisaturation of the corresponding old c-power, including n=0.

Every old odd c-walk avoids the full old K by the actual character
marking. If quotient d had an odd closed walk, the complete power
pullback would give an old odd c-walk with E-equivalent endpoints.
Since E <= K, this would contradict the old gate exclusion.
Therefore the selected REAL quotient d is bipartite, and the accepted
original parity seed theorem gives ACTUAL relative index two for the
even-walk / connectivity interval on every quotient point.

This constructs the parity interval on the already-built all-parent
quotient source. Identification with exact stable images e∨Y/e,
the actual selected occupancy-retyped source, original maximal gate
and entire safe tower remain separate C99–C105 obligations.
No quotient SAP, new source hypothesis, automorphism-section or
mixed reverse exact descent.
-/

universe u v w t

namespace CCO.ExactEPGeometry

open APCharacter
open APCharacter.Towers
open RigidGroupoid.Geometry
open CCO.ParityHasse.Original

noncomputable section

/-- The SAME actual source odd-pivot c and true quotient diversity atom d
have no odd quotient closed walks. Their actual quotient even/connectivity
equivalences have relative index TWO on every genuine quotient point.
The original E<=G hypothesis supplies E|p <= Kp, not quotient SAP. -/
theorem originalRetainedQuotientOddParity_indexTwo
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
      (∀ p q : Q.Point b.val,
        Q.source.atomRel d p q → ¬ Kq.rel p q) ∧
      (∀ q : Q.Point b.val, ∀ n : Nat,
        Odd n → ¬ relPow (Q.source.atomRel d) n q q) ∧
      ∀ q : Q.Point b.val,
        relativeIndex
          (evenColourEq Q.source Q.homogeneous d).val
          (connectivityColourEq Q.source Q.homogeneous d).val q = 2 := by
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
  obtain ⟨c,d,_hOldNonempty,hContained,hOutside,hPowers⟩ :=
    originalRetainedOddQuotientPowers
      A B P transport tp hOne Kroot phase E hE b
  have hNoOdd : ∀ q : Q.Point b.val, ∀ n : Nat,
      Odd n → ¬ relPow (Q.source.atomRel d) n q q := by
    intro q n hn hClosed
    obtain ⟨a,ha⟩ := Quotient.mk''_surjective q
    have hClosedA :
        relPow (Q.source.atomRel d) n
          (Quotient.mk'' a : Q.Point b.val)
          (Quotient.mk'' a : Q.Point b.val) := by
      simpa only [ha] using hClosed
    have hSat :
        setoidBiSaturation e (relPow (B.source.atomRel c) n) a a :=
      (hPowers n a a).mp hClosedA
    obtain ⟨u,v,hau,hPath,hva⟩ := hSat
    have hKua : K.rel u a := hNested (e.symm hau)
    have hKav : K.rel a v := hNested (e.symm hva)
    have hKuv : K.rel u v := K.setoid.trans hKua hKav
    exact (originalPhaseOddAtom_oddWalk_outsideGate
      B Kroot phase b c hContained n hn u v hPath) hKuv
  refine ⟨c,d,hOutside,hNoOdd,?_⟩
  intro q
  exact parity_seed_index_two Q.source Q.homogeneous d hNoOdd q

end
end CCO.ExactEPGeometry
