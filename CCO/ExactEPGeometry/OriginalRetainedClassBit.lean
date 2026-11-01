import CCO.ExactEPGeometry.OriginalRetainedCorrectedBit
import CCO.ExactEPGeometry.OriginalOccupancyRepresentatives

/-!
# B062 C80: an ACTUAL corrected bit on original E-classes

For one genuine retained source phase, choose any REAL reached
occupancy anchor a. Its exact local E-quotient points are the true
old E-classes meeting a, not invented point representatives.

Because E lies below the common original gate, the legal phase bit
is constant on each local E-class. Hence the real marked successor
provides a quotient function zeta on those actual E-classes.

For any E-related point x in another reached parent b, the
previously proved corrected-bit theorem identifies zeta of its
real anchor representative y with mark(x)+chi(I_ba). The actual
C49 full-class occupancy supplies y for each such x; no section
of the quotient automorphism group, SAP or unrealized marking
is inserted.
-/

universe u v w t

namespace CCO.ExactEPGeometry

open APCharacter
open APCharacter.SourceAge
open APCharacter.Towers
open RigidGroupoid.Geometry

noncomputable section

/-- C80: same ORIGINAL E-class in the ACTUAL anchor parent means
exactly the same real next-phase bit. The proof uses the full
E-class corrected-bit equality, not a guessed quotient marking. -/
theorem original_retained_anchor_Eclass_mark_eq
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
    (a : Reached B.source Kroot)
    (x y : B.Point a.val)
    (hxy : originalExactOnCurrentSort A B P transport
      (P.parent r) (fun k => hOne (P.parent r) k) E a.val x y) :
    UnarySource.mark (SingleStep.identification B phase)
      ⟨a.val,x⟩ =
    UnarySource.mark (SingleStep.identification B phase)
      ⟨a.val,y⟩ := by
  let J := originalExactOccupancySetoid
    A B P (P.parent r) (fun k => hOne (P.parent r) k) E
  have hGlobal : (currentOriginalExactSetoid A B P (P.parent r)
      (fun k => hOne (P.parent r) k) E).r
        (⟨a.val,x⟩ : Sigma B.Point)
        (⟨a.val,y⟩ : Sigma B.Point) :=
    (originalExactOnCurrentSort_iff A B P transport
      (P.parent r) (fun k => hOne (P.parent r) k)
      E a.val x y).mp hxy
  have hCorrected := original_retained_class_corrected_phase_invariant
    A B P transport tp hOne Kroot phase E hE
      a a a (J.refl a.val) (J.refl a.val) x y hGlobal
  exact add_right_cancel hCorrected

/-- The TRUE original E-class quotient of an active reached anchor
has an ACTUAL canonical corrected phase. This is a function on
E-classes, NOT a function chosen on representative old points. -/
noncomputable def originalRetainedAnchorClassBit
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
    (a : Reached B.source Kroot) :
    OriginalSelectedClass A B P transport
      (P.parent r) (fun k => hOne (P.parent r) k) E a.val →
        ZMod 2 :=
  Quotient.lift
    (fun x : B.Point a.val =>
      UnarySource.mark (SingleStep.identification B phase) ⟨a.val,x⟩)
    (fun x y hxy =>
      original_retained_anchor_Eclass_mark_eq A B P transport tp
        hOne Kroot phase E hE a x y hxy)

/-- Literal readout at the genuine local E-class point; this holds
by the precise Quotient.lift definition, not by an arbitrary choice
of a quotient section. -/
theorem originalRetainedAnchorClassBit_mk
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
    (a : Reached B.source Kroot) (y : B.Point a.val) :
    originalRetainedAnchorClassBit A B P transport tp hOne
      Kroot phase E hE a (Quotient.mk'' y) =
    UnarySource.mark (SingleStep.identification B phase)
      ⟨a.val,y⟩ := rfl

/-- C80 full classwise normalization: for a real E-pair from
an arbitrary active supported b to its actual anchor a,
the corrected bit of the b point equals the bit of the ACTUAL
anchor E-class. The phase character is taken on the true
complete current identity Arrow I_ba. -/
theorem originalRetainedAnchorClassBit_of_related
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
    (a b : Reached B.source Kroot)
    (hba : (originalExactOccupancySetoid A B P (P.parent r)
      (fun k => hOne (P.parent r) k) E).r b.val a.val)
    (x : B.Point b.val) (y : B.Point a.val)
    (hExy : (currentOriginalExactSetoid A B P (P.parent r)
      (fun k => hOne (P.parent r) k) E).r
        (⟨b.val,x⟩ : Sigma B.Point)
        (⟨a.val,y⟩ : Sigma B.Point)) :
    letI := Reached.groupoid B.homogeneous
      (exactCalculus_of_homogeneous_CCO
        B.source B.homogeneous B.cco) (A := Kroot)
    originalRetainedAnchorClassBit A B P transport tp hOne
      Kroot phase E hE a (Quotient.mk'' y) =
    UnarySource.mark (SingleStep.identification B phase)
      ⟨b.val,x⟩ +
      phase.character.value
        (original_retained_identity_arrow
          A B P transport tp hOne Kroot E hE b a hba) := by
  let J := originalExactOccupancySetoid
    A B P (P.parent r) (fun k => hOne (P.parent r) k) E
  have hCorrected :=
    original_retained_class_corrected_phase_invariant
      A B P transport tp hOne Kroot phase E hE
        a b a hba (J.refl a.val) x y hExy
  have hZero :=
    original_retained_anchor_gamma_zero
      A B P transport tp hOne Kroot phase E hE a
  rw [hZero] at hCorrected
  rw [originalRetainedAnchorClassBit_mk
    A B P transport tp hOne Kroot phase E hE a y]
  simpa only [add_zero] using hCorrected.symm

end
end CCO.ExactEPGeometry
