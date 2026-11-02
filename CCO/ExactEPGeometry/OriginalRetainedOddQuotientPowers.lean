import CCO.ExactEPGeometry.OriginalRetainedOddAtomicBlockImage
import CCO.ExactEPGeometry.OriginalQuotientOrbitalWalkPowers

/-!
# B062 C97–C98: the SAME actual reached odd pivot has exact quotient powers

The C97 theorem selects an actual old current atomic orbital c inside the
true distinguished odd SourcePhase Arrow at a reached parent and exactly
one genuine all-parent E-quotient diversity orbital d. Here the SAME
chosen c,d are retained and the previously proved C98 full E-saturation
power transport is applied to their actual nonempty old pair.

Every n, INCLUDING n=0, has literal pullback
    (d^n)|old = e;(c^n);e
on every old point pair. At zero this is the whole actual E-kernel.
The same d stays wholly outside the projected full K/e gate.

This is a genuine actual-source C97/C98 bridge, not a replacement for
C99 parity index-two or the C89–C96 entire locally admissible marked age.
No quotient SAP, new source assumption, group-action section, or mixed
reverse exact descent.
-/

universe u v w t

namespace CCO.ExactEPGeometry

open APCharacter
open APCharacter.Towers
open RigidGroupoid.Geometry
open CCO.ParityHasse.Original

noncomputable section

/-- One and the same genuine phase-odd old c and actual quotient
diversity d work for ALL n, and d remains outside the true full
projected K/e gate. The old setoid e is literally the original
E restriction on the reached current parent. -/
theorem originalRetainedOddQuotientPowers
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
      (∃ x y : B.Point b.val, B.source.atomRel c x y) ∧
      (∀ p q : Q.Point b.val,
        Q.source.atomRel d p q → ¬ Kq.rel p q) ∧
      ∀ (n : Nat) (a z : B.Point b.val),
        relPow (Q.source.atomRel d) n
          (Quotient.mk'' a : Q.Point b.val)
          (Quotient.mk'' z : Q.Point b.val) ↔
        setoidBiSaturation e
          (relPow (B.source.atomRel c) n) a z := by
  let base := P.parent r
  let hBase : ∀ i : A.Sorts, base = i := fun i => hOne base i
  let Q := originalExactAllCurrentQuotientCurrentSource
    A B P transport base hBase E
  let W := originalExactCurrentKernelWords
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
  obtain ⟨c,d,⟨x,y,hxy⟩,_hOldOut,_hQuotNonempty,hImage,hOutside⟩ :=
    originalRetainedOddAtomicBlock_imageQuotientDiversity
      A B P transport tp hOne Kroot phase E hE b
  have hSelfColour : Q.source.rawAtomRel
      (Q.source.colour (Quotient.mk'' x : Q.Point b.val)
        (Quotient.mk'' y : Q.Point b.val))
      (Quotient.mk'' x) (Quotient.mk'' y) := rfl
  have hOldBlock : Quotient.block B.source W (some c) x y := by
    have h := (originalExactAllCurrentPairBlock
      A B P transport base hBase E x x y y).mpr hSelfColour
    rw [hxy] at h
    exact h
  have hQuotAtom : Q.source.atomRel d
      (Quotient.mk'' x : Q.Point b.val)
      (Quotient.mk'' y : Q.Point b.val) := by
    apply (hImage (Quotient.mk'' x) (Quotient.mk'' y)).mp
    exact ⟨x,y,rfl,rfl,hOldBlock⟩
  have hOldColour : B.source.colour x y = some c := hxy
  have hQuotColour :
      (originalExactAllCurrentQuotientCurrentSource
        A B P transport base hBase E).source.colour
          (Quotient.mk'' x) (Quotient.mk'' y) = some d := hQuotAtom
  refine ⟨c,d,⟨x,y,hxy⟩,hOutside,?_⟩
  intro n a z
  have hPow := originalExactAllCurrentOrbitalRelPow_bisaturated_pullback
    A B P transport base hBase E x y n a z
  rw [hOldColour,hQuotColour] at hPow
  exact hPow

end
end CCO.ExactEPGeometry
