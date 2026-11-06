import CCO.ExactEPGeometry.OriginalPhaseEvenWalkGate
import CCO.ExactEPGeometry.OriginalRetainedQuotientParityProfiles

/-!
# B062 C100: the REAL projected K/e gate complements quotient parity

On the SAME genuinely reached SourcePhase parent and SAME selected
old atom c and quotient diversity atom d, C98–C99 give complete
E-bisaturated even/odd/connected profiles. The actual old odd Arrow
has square equal to the WHOLE source gate K; therefore all even
c-walks lie inside K, while all odd c-walks avoid it.

The exact pullback of the true full exact K/e gate then places the
entire quotient even profile below K/e. Since the entire quotient
odd profile is disjoint from K/e, the complete quotient connectivity
intersects K/e in exactly its quotient even profile:
   (K/e) ∩ barX = barY.
The same genuine quotient atom has parity relative index two.

This is the precise C100 complement identity, not yet C101 maximality.
No automatic quotient SAP, newly assumed complement, mixed reverse
exact descent, or chosen quotient-action section is used.
-/

universe u v w t

namespace CCO.ExactEPGeometry

open APCharacter
open APCharacter.Towers
open RigidGroupoid.Geometry
open CCO.ParityHasse.Original

noncomputable section

/-- A genuine projected RAW-full-exact K/e complements the actual
bipartite quotient pivot's entire even/connectivity interval.
Both the projected full gate and the parity interval are constructed
in their actual earlier quotient CurrentSource, not assumed. -/
theorem originalRetainedProjectedGate_parityComplement
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
      (∀ x y : B.Point b.val,
        B.source.atomRel c x y → (phase.atSort b).rel x y) ∧
      (∀ a z : B.Point b.val,
        OddWalk (Q.source.atomRel d)
            (Quotient.mk'' a : Q.Point b.val)
            (Quotient.mk'' z : Q.Point b.val) ↔
          setoidBiSaturation
            (originalExactCurrentKernelFamily
              A B P transport base hBase E b.val)
            (OddWalk (B.source.atomRel c)) a z) ∧
      (∀ p q : Q.Point b.val,
        Q.source.atomRel d p q → ¬ Kq.rel p q) ∧
      (∀ p q : Q.Point b.val,
        (Kq.rel p q ∧
          ConnectedWalk (Q.source.atomRel d) p q) ↔
            EvenWalk (Q.source.atomRel d) p q) ∧
      ∀ p : Q.Point b.val,
        relativeIndex
          (evenColourEq Q.source Q.homogeneous d).val
          (connectivityColourEq Q.source Q.homogeneous d).val p = 2 := by
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
  obtain ⟨c,d,hContained,hAtomOutside,hOddOutside,hIndex,hProfiles⟩ :=
    originalRetainedQuotientFullParityProfiles
      A B P transport tp hOne Kroot phase E hE b
  have hGatePull := originalCoherentAllparentProjectedKernel_pullback
    A B P transport tp base hBase E b.val K hNested
  have hEvenGate : ∀ p q : Q.Point b.val,
      EvenWalk (Q.source.atomRel d) p q → Kq.rel p q := by
    intro p q hEven
    obtain ⟨a,rfl⟩ := Quotient.mk''_surjective p
    obtain ⟨z,rfl⟩ := Quotient.mk''_surjective q
    obtain ⟨u,v,hau,hUV,hvz⟩ := (hProfiles a z).1.mp hEven
    have hKUV : K.rel u v :=
      originalPhaseOddAtom_evenWalk_inGate
        B Kroot phase b c hContained u v hUV
    have hKAZ : K.rel a z := K.setoid.trans (hNested hau)
      (K.setoid.trans hKUV (hNested hvz))
    exact (Iff.of_eq (congrFun (congrFun hGatePull a) z)).mpr hKAZ
  refine ⟨c,d,hContained,(fun a z => (hProfiles a z).2.1),hAtomOutside,?_,hIndex⟩
  intro p q
  constructor
  · rintro ⟨hGate,hConn⟩
    rcases (connectedWalk_iff_even_or_odd
      (Q.source.atomRel d) p q).mp hConn with he | ho
    · exact he
    · exact False.elim (hOddOutside p q ho hGate)
  · intro he
    exact ⟨hEvenGate p q he,
      (connectedWalk_iff_even_or_odd
        (Q.source.atomRel d) p q).mpr (Or.inl he)⟩

end
end CCO.ExactEPGeometry
