import CCO.ExactEPGeometry.OriginalRetainedClassBit
import Mathlib.Tactic.Abel

/-!
# B062 C80 and C94: correction of EVERY genuine original global marking

The original C80 class-bit construction was proved for the canonical
genuine successor marking. The quotient marked-age converse C93–C95
needs its statement for ANY global bit function satisfying the
ACTUAL original maximal-character masks, not just that one successor.
This is a real universal source fact, proved using the whole canonical
old gate identity bridges, their genuine original G trace, original
full-groupoid character cocycle and literal source SourcePhase masks.

On each actual original E-class, the corrected phase value descends
to a well-defined function on the *real* E-quotient, and agrees
across every E-supported reached parent with the true C79 offset.
No quotient SAP, cross-sort synthetic atom, automorphism-group
section, extra exactness premise, or hypothetical marked quotient
source is added.

Producing one original global marking FROM a selected quotient
marking with prescribed quotient bits is a distinct C93–C94
obligation, not assumed here.
-/

universe u v w t

namespace CCO.ExactEPGeometry

open APCharacter
open APCharacter.Towers
open RigidGroupoid.Geometry

noncomputable section

/-- Every genuine original global character-compatible marking,
not only the canonical marked successor, has ONE corrected value
on all real points in a common original E-class and occupancy
component. The exact identity bridge I_bc is a WHOLE relation
with real witnesses, not a pointwise function. -/
theorem originalRetainedAnyMarkCorrectedInvariant
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
    (mark : Sigma B.Point → ZMod 2)
    (hMark : phase.masks.GlobalMarking mark)
    (a b c : Reached B.source Kroot)
    (hba : (originalExactOccupancySetoid A B P (P.parent r)
      (fun k => hOne (P.parent r) k) E).r b.val a.val)
    (hca : (originalExactOccupancySetoid A B P (P.parent r)
      (fun k => hOne (P.parent r) k) E).r c.val a.val)
    (x : B.Point b.val) (y : B.Point c.val)
    (hExy : (currentOriginalExactSetoid A B P (P.parent r)
      (fun k => hOne (P.parent r) k) E).r
      (⟨b.val,x⟩ : Sigma B.Point)
      (⟨c.val,y⟩ : Sigma B.Point)) :
    letI := Reached.groupoid B.homogeneous
      (exactCalculus_of_homogeneous_CCO
        B.source B.homogeneous B.cco) (A := Kroot)
    mark ⟨b.val,x⟩ +
      phase.character.value
        (original_retained_identity_arrow
          A B P transport tp hOne Kroot E hE b a hba) =
    mark ⟨c.val,y⟩ +
      phase.character.value
        (original_retained_identity_arrow
          A B P transport tp hOne Kroot E hE c a hca) := by
  let C := exactCalculus_of_homogeneous_CCO
    B.source B.homogeneous B.cco
  letI := Reached.groupoid B.homogeneous C (A := Kroot)
  let J := originalExactOccupancySetoid
    A B P (P.parent r) (fun k => hOne (P.parent r) k) E
  let hbc : J.r b.val c.val := J.trans hba (J.symm hca)
  let Ibc := original_retained_identity_arrow
    A B P transport tp hOne Kroot E hE b c hbc
  let Iba := original_retained_identity_arrow
    A B P transport tp hOne Kroot E hE b a hba
  let Ica := original_retained_identity_arrow
    A B P transport tp hOne Kroot E hE c a hca
  let G := PrefixExactLargestLift.largest A B P transport tp r
    (current_kernel_exact_eq B Kroot)
  let JG := currentOriginalExactSetoid A B P (P.parent r)
    (fun k => hOne (P.parent r) k) G
  have hGxy : JG.r
      (⟨b.val,x⟩ : Sigma B.Point)
      (⟨c.val,y⟩ : Sigma B.Point) := hE hExy
  have hR : Ibc.rel x y :=
    (original_retained_identity_arrow_global_iff
      A B P transport tp hOne Kroot E hE b c hbc x y).mpr hGxy
  have hLegal : phase.allows (B.source.colour x y)
      (mark ⟨b.val,x⟩) (mark ⟨c.val,y⟩) :=
    hMark.2 (⟨b.val,x⟩ : Sigma B.Point)
      (⟨c.val,y⟩ : Sigma B.Point)
  have hRead := (phase.rigid_mask_iff b c Ibc x y hR
    (mark ⟨b.val,x⟩) (mark ⟨c.val,y⟩)).mp hLegal
  have hBits : mark ⟨c.val,y⟩ =
      mark ⟨b.val,x⟩ + phase.character.value Ibc := hRead.2.2
  have hGamma : phase.character.value Ibc =
      phase.character.value Iba + phase.character.value Ica :=
    original_retained_gamma_add
      A B P transport tp hOne Kroot phase E hE a b c hba hca
  have hDouble : ∀ z : ZMod 2, z + z = 0 := by decide
  calc
    mark ⟨b.val,x⟩ + phase.character.value Iba =
        mark ⟨b.val,x⟩ +
          (phase.character.value Iba +
            (phase.character.value Ica + phase.character.value Ica)) := by
      rw [hDouble]
      simp
    _ = (mark ⟨b.val,x⟩ +
          (phase.character.value Iba + phase.character.value Ica)) +
            phase.character.value Ica := by abel
    _ = (mark ⟨b.val,x⟩ +
          phase.character.value Ibc) + phase.character.value Ica := by
      rw [hGamma]
    _ = mark ⟨c.val,y⟩ + phase.character.value Ica := by
      rw [hBits]

/-- C94's equality of every actual original global marking on
two members of one original E-class in the SAME reached sort. -/
theorem originalRetainedAnyMarkAnchorEclassEq
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
    (mark : Sigma B.Point → ZMod 2)
    (hMark : phase.masks.GlobalMarking mark)
    (a : Reached B.source Kroot)
    (x y : B.Point a.val)
    (hxy : originalExactOnCurrentSort A B P transport
      (P.parent r) (fun k => hOne (P.parent r) k) E a.val x y) :
    mark ⟨a.val,x⟩ = mark ⟨a.val,y⟩ := by
  let J := originalExactOccupancySetoid
    A B P (P.parent r) (fun k => hOne (P.parent r) k) E
  have hGlobal : (currentOriginalExactSetoid A B P (P.parent r)
      (fun k => hOne (P.parent r) k) E).r
        (⟨a.val,x⟩ : Sigma B.Point)
        (⟨a.val,y⟩ : Sigma B.Point) :=
    (originalExactOnCurrentSort_iff A B P transport
      (P.parent r) (fun k => hOne (P.parent r) k)
      E a.val x y).mp hxy
  have hCorrected := originalRetainedAnyMarkCorrectedInvariant
    A B P transport tp hOne Kroot phase E hE mark hMark
      a a a (J.refl a.val) (J.refl a.val) x y hGlobal
  exact add_right_cancel hCorrected

/-- From ANY actual original globally admissible phase marking,
construct its REAL pointwise class function on the local E-quotient
of the reached anchor. This is literal Quotient.lift with the
previously PROVED constancy, not a set-theoretic section. -/
noncomputable def originalRetainedAnyMarkAnchorClassBit
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
    (mark : Sigma B.Point → ZMod 2)
    (hMark : phase.masks.GlobalMarking mark)
    (a : Reached B.source Kroot) :
    OriginalSelectedClass A B P transport
      (P.parent r) (fun k => hOne (P.parent r) k) E a.val →
        ZMod 2 :=
  Quotient.lift
    (fun x : B.Point a.val => mark ⟨a.val,x⟩)
    (fun x y hxy =>
      originalRetainedAnyMarkAnchorEclassEq
        A B P transport tp hOne Kroot phase E hE mark hMark
          a x y hxy)

/-- The actual E-quotient class value reproduces its original
global marking on each old representative, without dependence
on that representative's choice. -/
theorem originalRetainedAnyMarkAnchorClassBit_mk
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
    (mark : Sigma B.Point → ZMod 2)
    (hMark : phase.masks.GlobalMarking mark)
    (a : Reached B.source Kroot) (y : B.Point a.val) :
    originalRetainedAnyMarkAnchorClassBit A B P transport tp hOne
      Kroot phase E hE mark hMark a (Quotient.mk'' y) =
    mark ⟨a.val,y⟩ := rfl

/-- All E-supported reached parents compute the SAME corrected
value of an arbitrary globally legal original marking. C79's
whole identity bridge supplies the exact objectwise offset. -/
theorem originalRetainedAnyMarkAnchorClassBit_of_related
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
    (mark : Sigma B.Point → ZMod 2)
    (hMark : phase.masks.GlobalMarking mark)
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
    originalRetainedAnyMarkAnchorClassBit A B P transport tp hOne
      Kroot phase E hE mark hMark a (Quotient.mk'' y) =
    mark ⟨b.val,x⟩ +
      phase.character.value
        (original_retained_identity_arrow
          A B P transport tp hOne Kroot E hE b a hba) := by
  let J := originalExactOccupancySetoid
    A B P (P.parent r) (fun k => hOne (P.parent r) k) E
  have hCorrected := originalRetainedAnyMarkCorrectedInvariant
    A B P transport tp hOne Kroot phase E hE mark hMark
      a b a hba (J.refl a.val) x y hExy
  have hZero := original_retained_anchor_gamma_zero
    A B P transport tp hOne Kroot phase E hE a
  rw [hZero] at hCorrected
  rw [originalRetainedAnyMarkAnchorClassBit_mk
    A B P transport tp hOne Kroot phase E hE mark hMark a y]
  simpa only [add_zero] using hCorrected.symm

end
end CCO.ExactEPGeometry
