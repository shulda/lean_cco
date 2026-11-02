import CCO.ExactEPGeometry.OriginalRetainedProjectedOddDominance
import CCO.ParityHasse.Original.ParitySeed

/-!
# B062 C101: the genuine projected full-exact K/E is a MAXIMAL complement

On the previously built actual all-parent E-quotient, take precisely
the source-selected old phase-odd c and genuine quotient diversity d
from the C100 complement theorem, retaining its C97–C99 whole-orbital
odd-profile pullback. The complete projected K/E is FULL RAW exact and
complements the genuine index-two even/connectivity interval.

Any STRICTLY larger quotient full-exact equivalence Z has a full-exact
old pullback W>K by the actual C101 I10 provider. The original
phase atSort dominance forces every old c edge into W. Therefore
every old odd c-walk and its E-saturation is in W, so at least one
ACTUAL quotient d-edge belongs to Z. That edge is connected but not
even: even walks are inside K/E while d is disjoint from K/E.
Consequently Z is NOT a parity complement. This proves maximality
among ALL full-exact quotient equivalences, not merely one selected
lift. No SAP, automorphism section or extra source premise.
The selected one-sort-per-E-occupancy retyping and entire marked
quotient age remain separate obligations.
-/

universe u v w t

namespace CCO.ExactEPGeometry

open APCharacter
open APCharacter.Towers
open RigidGroupoid.Geometry
open CCO.ParityHasse.Original

noncomputable section

/-- C101: same genuine C100 quotient d, with actual relative index two,
is complemented by K/E, and NO strictly larger full RAW-exact quotient
equivalence can still complement its even/connectivity interval. -/
theorem originalRetainedProjectedGate_maximalParityComplement
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
    letI : PartialOrder (Kernel Q.source b.val) :=
      kernelPartialOrder Q.source b.val
    ∃ (c : B.source.Atom b.val b.val)
      (d : Q.source.Atom b.val b.val),
      (∀ p q : Q.Point b.val,
        Q.source.atomRel d p q → ¬ Kq.rel p q) ∧
      (∀ p q : Q.Point b.val,
        (Kq.rel p q ∧ ConnectedWalk (Q.source.atomRel d) p q) ↔
          EvenWalk (Q.source.atomRel d) p q) ∧
      (∀ p : Q.Point b.val,
        relativeIndex
          (evenColourEq Q.source Q.homogeneous d).val
          (connectivityColourEq Q.source Q.homogeneous d).val p = 2) ∧
      ∀ Z : Kernel Q.source b.val, Kq < Z →
        ¬ ∀ p q : Q.Point b.val,
          (Z.rel p q ∧ ConnectedWalk (Q.source.atomRel d) p q) ↔
            EvenWalk (Q.source.atomRel d) p q := by
  let base := P.parent r
  let hBase : ∀ i : A.Sorts, base = i := fun i => hOne base i
  let Q := originalExactAllCurrentQuotientCurrentSource
    A B P transport base hBase E
  letI : PartialOrder (Kernel Q.source b.val) :=
    kernelPartialOrder Q.source b.val
  letI : PartialOrder (Kernel B.source b.val) :=
    kernelPartialOrder B.source b.val
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
  obtain ⟨c,d,hContained,hOddProfile,hOutside,hComplement,hIndex⟩ :=
    originalRetainedProjectedGate_parityComplement
      A B P transport tp hOne Kroot phase E hE b
  refine ⟨c,d,hOutside,hComplement,hIndex,?_⟩
  intro Z hStrict hCandidate
  obtain ⟨p,q,hAtom⟩ := Q.source.realized d
  obtain ⟨a,rfl⟩ := Quotient.mk''_surjective p
  obtain ⟨z,rfl⟩ := Quotient.mk''_surjective q
  have hOdd : OddWalk (Q.source.atomRel d) (pi a) (pi z) :=
    ⟨1,odd_one,(relPow_one (Q.source.atomRel d) (pi a) (pi z)).mpr hAtom⟩
  have hSat : setoidBiSaturation e (OddWalk (B.source.atomRel c)) a z :=
    (hOddProfile a z).mp hOdd
  obtain ⟨u,v,hau,⟨n,hn,hPath⟩,hvz⟩ := hSat
  let Zpre : Setoid (B.Point b.val) := Setoid.comap pi Z.setoid
  have hEdge : ∀ x y : B.Point b.val,
      B.source.atomRel c x y → Zpre.r x y := by
    intro x y hxy
    exact originalRetainedProjectedOdd_dominatesStrictGate
      A B P transport tp hOne Kroot phase E hE b
        Z hStrict x y (hContained x y hxy)
  have hUV : Zpre.r u v :=
    relPow_le_setoid (B.source.atomRel c) Zpre hEdge n u v hPath
  have hAU : Zpre.r a u := by
    change Z.rel (pi a) (pi u)
    have heq : pi a = pi u := Quotient.sound hau
    rw [heq]
    exact Z.setoid.refl (pi u)
  have hVZ : Zpre.r v z := by
    change Z.rel (pi v) (pi z)
    have heq : pi v = pi z := Quotient.sound hvz
    rw [heq]
    exact Z.setoid.refl (pi z)
  have hAZ : Zpre.r a z := Zpre.trans hAU (Zpre.trans hUV hVZ)
  have hZ : Z.rel (pi a) (pi z) := hAZ
  have hConnected : ConnectedWalk (Q.source.atomRel d) (pi a) (pi z) :=
    ⟨1,(relPow_one (Q.source.atomRel d) (pi a) (pi z)).mpr hAtom⟩
  have hEven : EvenWalk (Q.source.atomRel d) (pi a) (pi z) :=
    (hCandidate (pi a) (pi z)).mp ⟨hZ,hConnected⟩
  have hK : Kq.rel (pi a) (pi z) :=
    ((hComplement (pi a) (pi z)).mpr hEven).1
  exact hOutside (pi a) (pi z) hAtom hK

end
end CCO.ExactEPGeometry
