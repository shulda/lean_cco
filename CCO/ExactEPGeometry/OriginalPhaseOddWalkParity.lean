import CCO.ExactEPGeometry.OriginalRetainedOddQuotientPowers
import CCO.RigidGroupoid.Phase.ActualPhase
import CCO.ParityHasse.Original.ParitySeed

/-!
# B062 C99: true SourcePhase odd-arrow atom walks avoid the FULL reached gate

A real global marking of the free reached rigid groupoid exists for
the ACTUAL SourcePhase character. Every edge in its distinguished odd
Arrow has character 1 and flips this genuine point marking; every
pair inside the whole reached gate has the same marking. Hence no
odd-length walk made of an atom contained in that odd Arrow can lie
inside the gate, including a closed walk. This uses neither quotient
SAP nor an ad hoc colouring of points; the marking is supplied by
the proved full-character free-action provider.

The next C99 consumer must attach this to the exact SAME c,d chosen in
C97/C98 and transfer the conclusion to quotient odd powers via the
already proved complete E-saturated power equation.
-/

universe u v w t

namespace CCO.ExactEPGeometry

open APCharacter
open APCharacter.Towers
open RigidGroupoid.Geometry
open CategoryTheory
open CCO.ParityHasse.Original

noncomputable section

/-- In F_2, a path whose every edge flips a genuine bit changes that bit
by the parity of its exact length. In particular odd length cannot
connect two points with the SAME bit. -/
theorem oddWalk_changesBit
    {X : Type*} (R : X → X → Prop) (bit : X → ZMod 2)
    (hFlip : ∀ a b, R a b → bit b = bit a + 1)
    {n : Nat} {x y : X} (hn : Odd n) (hWalk : relPow R n x y) :
    bit x ≠ bit y := by
  have hAll : ∀ m : Nat, ∀ a b : X,
      relPow R m a b → bit b = bit a + (m : ZMod 2) := by
    intro m
    induction m with
    | zero =>
        intro a b hab
        have heq : a = b := hab
        subst b
        simp
    | succ m ih =>
        intro a b hab
        obtain ⟨z,haz,hzb⟩ := hab
        calc
          bit b = bit z + (m : ZMod 2) := ih z b hzb
          _ = (bit a + 1) + (m : ZMod 2) := by rw [hFlip a z haz]
          _ = bit a + ((m+1 : Nat) : ZMod 2) := by
            rw [Nat.cast_add, Nat.cast_one]
            abel
  have hone : (n : ZMod 2) = 1 := by
    obtain ⟨k,hk⟩ := hn
    rw [hk, Nat.cast_add, Nat.cast_mul]
    have htwo : (2 : ZMod 2) = 0 := by decide
    simp [htwo]
  intro heq
  have h := hAll n x y hWalk
  rw [hone,←heq] at h
  have hzero : bit x + 0 = bit x + 1 := by simpa only [add_zero] using h
  have hfalse : (0 : ZMod 2) = 1 := add_left_cancel hzero
  exact zero_ne_one hfalse

/-- Any old current atom literally lying in the distinguished
SourcePhase odd whole Arrow has ALL its odd powers disjoint from the
entire reached K, not just from logical equality. Uses a genuine
global marking of the actual groupoid, and the SAME phase character
detecting its distinguished Arrow. -/
theorem originalPhaseOddAtom_oddWalk_outsideGate
    (B : CurrentSource.{u,v,w,t})
    {r : B.Sorts} (Kroot : Kernel B.source r)
    (phase : SourcePhase B.source B.homogeneous
      (exactCalculus_of_homogeneous_CCO
        B.source B.homogeneous B.cco) Kroot)
    (b : Reached B.source Kroot)
    (c : B.source.Atom b.val b.val)
    (hContained : ∀ x y : B.Point b.val,
      B.source.atomRel c x y → (phase.atSort b).rel x y)
    (n : Nat) (hn : Odd n)
    (x y : B.Point b.val)
    (hWalk : relPow (B.source.atomRel c) n x y) :
    ¬ (Reached.kernel B.homogeneous
      (exactCalculus_of_homogeneous_CCO
        B.source B.homogeneous B.cco) b).rel x y := by
  let C := exactCalculus_of_homogeneous_CCO
    B.source B.homogeneous B.cco
  let K := Reached.kernel B.homogeneous C b
  letI : Groupoid (Reached B.source Kroot) :=
    Reached.groupoid B.homogeneous C (A := Kroot)
  obtain ⟨mark,hMark⟩ :=
    RigidGroupoid.Phase.actual_global_marking
      B.source B.homogeneous C Kroot phase.character
  let bit : B.Point b.val → ZMod 2 := fun a =>
    RigidGroupoid.Phase.originalMarking
      B.source B.homogeneous C Kroot mark ⟨b.val,a⟩
  have hFlip : ∀ a z : B.Point b.val,
      B.source.atomRel c a z → bit z = bit a + 1 := by
    intro a z hac
    have hArrow :=
      RigidGroupoid.Phase.originalMarking_arrow_equation
        B.source B.homogeneous C Kroot phase.character mark hMark
        (phase.atSort b) a z (hContained a z hac)
    have hDetect : phase.character.value (phase.atSort b) = 1 :=
      phase.atSort_detects b
    change bit z = bit a + phase.character.value (phase.atSort b) at hArrow
    rw [hDetect] at hArrow
    exact hArrow
  have hDifferent : bit x ≠ bit y :=
    oddWalk_changesBit (B.source.atomRel c) bit hFlip hn hWalk
  intro hGate
  have hSame : bit x = bit y :=
    RigidGroupoid.Phase.originalMarking_constant
      B.source B.homogeneous C Kroot mark b x y hGate
  exact hDifferent hSame

end
end CCO.ExactEPGeometry
