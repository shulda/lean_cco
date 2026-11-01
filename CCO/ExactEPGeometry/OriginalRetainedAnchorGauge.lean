import CCO.ExactEPGeometry.SelectedGaugeCharacter
import CCO.ExactEPGeometry.OriginalRetainedGamma

/-!
# B062 C84: actual corrected character of a retained E-occupancy component

The FULL source phase character and the ORIGINAL E-supported whole gate
identity arrows I_ba were already constructed and proved to compose
(C78–C79). Fix one actual Reached parent a. On its real E-occupancy
component, gamma_b is the ACTUAL original phase value chi(I_ba);
outside this component an arbitrary zero offset suffices to define
a character on the whole old Reached groupoid.

The C79 source cocycle chi(I_bc)=gamma_b+gamma_c makes the genuinely
constructed normalized character zero on EVERY complete old gate
identity bridge in this supported component. This is a source-level
first C84 characterization, not yet the quotient of the object
category, the corrected finite-age masks, or the full tower converse.
No quotient SAP, new phase hypothesis, chosen automorphism section,
invented identity orbital, or conditional bridge is used.
-/

universe u v w t

namespace CCO.ExactEPGeometry

open APCharacter
open APCharacter.Towers
open RigidGroupoid.Geometry
open CCO.RigidGroupoid.Phase

noncomputable section

/-- A TRUE C79 phase normalization on the E-occupancy component of
a fixed actual reached anchor. Its value at each supported b is
the complete source character of the actual I_ba Arrow. -/
noncomputable def originalRetainedAnchorOffset
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
    (a b : Reached B.source Kroot) : ZMod 2 := by
  let C := exactCalculus_of_homogeneous_CCO
    B.source B.homogeneous B.cco
  letI := Reached.groupoid B.homogeneous C (A := Kroot)
  let J := originalExactOccupancySetoid
    A B P (P.parent r) (fun k => hOne (P.parent r) k) E
  exact if hba : J.r b.val a.val then
    phase.character.value
      (original_retained_identity_arrow
        A B P transport tp hOne Kroot E hE b a hba)
    else 0

/-- Every offset on the displayed real E-supported component is
the ACTUAL C79 identity-bridge character, not an arbitrary label. -/
theorem originalRetainedAnchorOffset_supported
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
      (fun k => hOne (P.parent r) k) E).r b.val a.val) :
    letI := Reached.groupoid B.homogeneous
      (exactCalculus_of_homogeneous_CCO
        B.source B.homogeneous B.cco) (A := Kroot)
    originalRetainedAnchorOffset A B P transport tp
      hOne Kroot phase E hE a b =
    phase.character.value
      (original_retained_identity_arrow
        A B P transport tp hOne Kroot E hE b a hba) := by
  dsimp only
  unfold originalRetainedAnchorOffset
  simp only [dif_pos hba]

/-- The true anchor has gamma_a = chi(I_aa) = 0,
where the groupoid identity is the whole original gate. -/
theorem originalRetainedAnchorOffset_anchor_zero
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
    originalRetainedAnchorOffset A B P transport tp
      hOne Kroot phase E hE a a = 0 := by
  let J := originalExactOccupancySetoid
    A B P (P.parent r) (fun k => hOne (P.parent r) k) E
  rw [originalRetainedAnchorOffset_supported
    A B P transport tp hOne Kroot phase E hE a a (J.refl a.val)]
  exact original_retained_anchor_gamma_zero
    A B P transport tp hOne Kroot phase E hE a

/-- Every actual full-reached Hom receives the genuine C84
objectwise corrected source character. The actual offsets are
constructed from complete old-gate bridges wherever E-supported. -/
noncomputable def originalRetainedAnchoredCharacter
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
    letI := Reached.groupoid B.homogeneous
      (exactCalculus_of_homogeneous_CCO
        B.source B.homogeneous B.cco) (A := Kroot)
    Abstract.Character (Reached B.source Kroot) := by
  let C := exactCalculus_of_homogeneous_CCO
    B.source B.homogeneous B.cco
  letI := Reached.groupoid B.homogeneous C (A := Kroot)
  exact gaugeCharacter phase.character
    (fun b => originalRetainedAnchorOffset A B P transport tp
      hOne Kroot phase E hE a b)

/-- Actual local C84 identity collapse: whenever two genuine reached
parents b,c belong to the E-occupancy component of anchor a, the
normalized character vanishes on their WHOLE gate identity Arrow.
The original phase identity value itself may be nonzero; its TWO
real endpoint offsets correct it exactly by the C79 cocycle. -/
theorem originalRetainedAnchoredCharacter_identity_zero
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
    (a b c : Reached B.source Kroot)
    (hba : (originalExactOccupancySetoid A B P (P.parent r)
      (fun k => hOne (P.parent r) k) E).r b.val a.val)
    (hca : (originalExactOccupancySetoid A B P (P.parent r)
      (fun k => hOne (P.parent r) k) E).r c.val a.val) :
    let J := originalExactOccupancySetoid A B P (P.parent r)
      (fun k => hOne (P.parent r) k) E
    letI := Reached.groupoid B.homogeneous
      (exactCalculus_of_homogeneous_CCO
        B.source B.homogeneous B.cco) (A := Kroot)
    (originalRetainedAnchoredCharacter A B P transport tp
      hOne Kroot phase E hE a).value
      (original_retained_identity_arrow A B P transport tp
        hOne Kroot E hE b c (J.trans hba (J.symm hca))) = 0 := by
  dsimp only
  let C := exactCalculus_of_homogeneous_CCO
    B.source B.homogeneous B.cco
  letI := Reached.groupoid B.homogeneous C (A := Kroot)
  let J := originalExactOccupancySetoid A B P (P.parent r)
    (fun k => hOne (P.parent r) k) E
  let gamma : Reached B.source Kroot → ZMod 2 :=
    fun d => originalRetainedAnchorOffset A B P transport tp
      hOne Kroot phase E hE a d
  let Ibc := original_retained_identity_arrow A B P transport tp
    hOne Kroot E hE b c (J.trans hba (J.symm hca))
  have hb : gamma b = phase.character.value
      (original_retained_identity_arrow A B P transport tp
        hOne Kroot E hE b a hba) :=
    originalRetainedAnchorOffset_supported
      A B P transport tp hOne Kroot phase E hE a b hba
  have hc : gamma c = phase.character.value
      (original_retained_identity_arrow A B P transport tp
        hOne Kroot E hE c a hca) :=
    originalRetainedAnchorOffset_supported
      A B P transport tp hOne Kroot phase E hE a c hca
  have hIbc : phase.character.value Ibc = gamma b + gamma c := by
    calc
      phase.character.value Ibc =
          phase.character.value
            (original_retained_identity_arrow A B P transport tp
              hOne Kroot E hE b a hba) +
          phase.character.value
            (original_retained_identity_arrow A B P transport tp
              hOne Kroot E hE c a hca) :=
        original_retained_gamma_add A B P transport tp
          hOne Kroot phase E hE a b c hba hca
      _ = gamma b + gamma c := by rw [hb,hc]
  change (gaugeCharacter phase.character gamma).value Ibc = 0
  exact gaugeCharacter_bridge_zero phase.character gamma Ibc hIbc

end
end CCO.ExactEPGeometry
