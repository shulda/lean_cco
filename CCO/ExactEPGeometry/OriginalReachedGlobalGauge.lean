import CCO.ExactEPGeometry.OriginalReachedOccupancyAnchors

/-!
# B062 C84: one genuine corrected phase on ALL reached E-components

Choose an actual Reached anchor in EACH literal original E-occupancy
component, using the proved quotient of all reached source objects.
For every reached b, define gamma_b as the original full SourcePhase
character on the genuine old-gate bridge I_(b,anchor[b]).
C79 proves the real identity bridge cocycle; C49 proves that two
E-supported reached parents use LITERALLY the same selected anchor.

This gives ONE corrected character on the ENTIRE old full Reached
groupoid, with ZERO value on EVERY identity gate bridge I_bc
whenever b and c have the same real original E-occupancy support.
The original exact gate is never replaced by logical identity.
This is a precise C84 phase-source obligation, not yet the quotient
object category, full quotient phase masks, or the finite-age converse.
No quotient SAP, automorphism section, invented sorting or new axioms.
-/

universe u v w t

namespace CCO.ExactEPGeometry

open APCharacter
open APCharacter.Towers
open RigidGroupoid.Geometry
open CCO.RigidGroupoid.Phase

noncomputable section

/-- The global C84 offset on EVERY actual reached object, obtained by
choosing its REAL E-occupancy component's own reached anchor. This is
the genuine original character of the entire I_(b,anchor[b]) Arrow. -/
noncomputable def originalReachedGlobalOffset
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
    (b : Reached B.source Kroot) : ZMod 2 :=
  originalRetainedAnchorOffset A B P transport tp
    hOne Kroot phase E hE
    (originalReachedOccupancyAnchorOf A B P (P.parent r)
      (fun k => hOne (P.parent r) k) E Kroot b) b

/-- A single REAL corrected character, simultaneously defined on the
WHOLE full Reached groupoid: the C79 phases at distinct E-components
are selected independently, but all morphisms retain the original
complete character via the universal gaugeCharacter construction. -/
noncomputable def originalReachedGlobalCharacter
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
      (current_kernel_exact_eq B Kroot)) :
    letI := Reached.groupoid B.homogeneous
      (exactCalculus_of_homogeneous_CCO
        B.source B.homogeneous B.cco) (A := Kroot)
    Abstract.Character (Reached B.source Kroot) := by
  let C := exactCalculus_of_homogeneous_CCO
    B.source B.homogeneous B.cco
  letI := Reached.groupoid B.homogeneous C (A := Kroot)
  exact gaugeCharacter phase.character
    (originalReachedGlobalOffset A B P transport tp
      hOne Kroot phase E hE)

/-- The C84 crucial global source statement: EVERY actual complete
identity Arrow I_bc between E-occupancy equivalent reached parents
has corrected phase ZERO, with no assumption that b and c belong
to a previously fixed selected component or are generating edges.
The source phase on unrelated arrows remains genuinely defined by
the same global character and its true composition law. -/
theorem originalReachedGlobalCharacter_identity_zero
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
    (b c : Reached B.source Kroot)
    (hbc : (originalExactOccupancySetoid A B P (P.parent r)
      (fun k => hOne (P.parent r) k) E).r b.val c.val) :
    letI := Reached.groupoid B.homogeneous
      (exactCalculus_of_homogeneous_CCO
        B.source B.homogeneous B.cco) (A := Kroot)
    (originalReachedGlobalCharacter A B P transport tp
      hOne Kroot phase E hE).value
      (original_retained_identity_arrow A B P transport tp
        hOne Kroot E hE b c hbc) = 0 := by
  let C := exactCalculus_of_homogeneous_CCO
    B.source B.homogeneous B.cco
  letI := Reached.groupoid B.homogeneous C (A := Kroot)
  let J := originalExactOccupancySetoid A B P (P.parent r)
    (fun k => hOne (P.parent r) k) E
  let anchor : Reached B.source Kroot → Reached B.source Kroot :=
    originalReachedOccupancyAnchorOf A B P (P.parent r)
      (fun k => hOne (P.parent r) k) E Kroot
  let a := anchor b
  let gamma : Reached B.source Kroot → ZMod 2 :=
    originalReachedGlobalOffset A B P transport tp
      hOne Kroot phase E hE
  have hba : J.r b.val a.val :=
    originalReachedOccupancyAnchorOf_supported A B P
      (P.parent r) (fun k => hOne (P.parent r) k) E Kroot b
  have hca : J.r c.val a.val := J.trans (J.symm hbc) hba
  have hAnchor : anchor b = anchor c :=
    originalReachedOccupancyAnchorOf_eq A B P
      (P.parent r) (fun k => hOne (P.parent r) k) E Kroot b c hbc
  have hb : gamma b =
      originalRetainedAnchorOffset A B P transport tp
        hOne Kroot phase E hE a b := rfl
  have hc : gamma c =
      originalRetainedAnchorOffset A B P transport tp
        hOne Kroot phase E hE a c := by
    change originalRetainedAnchorOffset A B P transport tp
      hOne Kroot phase E hE (anchor c) c =
      originalRetainedAnchorOffset A B P transport tp
        hOne Kroot phase E hE (anchor b) c
    rw [← hAnchor]
  let Ibc := original_retained_identity_arrow A B P transport tp
    hOne Kroot E hE b c hbc
  have hValue : phase.character.value Ibc = gamma b + gamma c := by
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
      _ = originalRetainedAnchorOffset A B P transport tp
            hOne Kroot phase E hE a b +
          originalRetainedAnchorOffset A B P transport tp
            hOne Kroot phase E hE a c := by
        rw [originalRetainedAnchorOffset_supported A B P transport tp
          hOne Kroot phase E hE a b hba,
          originalRetainedAnchorOffset_supported A B P transport tp
          hOne Kroot phase E hE a c hca]
      _ = gamma b + gamma c := by rw [hb,hc]
  change (gaugeCharacter phase.character gamma).value Ibc = 0
  exact gaugeCharacter_bridge_zero phase.character gamma Ibc hValue

end
end CCO.ExactEPGeometry
