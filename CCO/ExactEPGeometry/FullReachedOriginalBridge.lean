import CCO.ExactEPGeometry.OriginalArrowReverseBridge
import CCO.APCharacter.SourcePhase

/-!
# B062 C57–C58: ALL actual full current bridges and ORIGINAL correspondences

For the ACTUAL connected full rigid-groupoid source reached from a
genuine current exact gate, every pair of objects has a literal
current `Reached.connectingArrow`. The already proved C55/C56 results
identify its common canonical ORIGINAL full-RAW-exact gate, with the
correct source and target current restrictions.

Here BOTH directions of the exact correspondence theorem are proved
for ALL actual full homs:
* every current full Arrow has a whole original G-Arrow whose complete
  p,q trace is exactly its current relation;
* every old full G-Arrow with a REAL nonempty p,q trace produces an
  actual full current Arrow, with all four equations proved by C57's
  genuinely guarded displayed-middle (TP).

The original one-sort condition is explicit, matching the frozen B062
source. It is NOT imposed on arbitrary typed sources or quotients.
No SAP, selected generating subset, imaginary representative section,
arbitrary mixed reverse exactness, or new axiom.
-/

universe u v w t

namespace CCO.ExactEPGeometry

open APCharacter
open APCharacter.Towers
open RigidGroupoid.Geometry

noncomputable section

/-- C57–C58 for the FULL actual connected exact rigid groupoid.
The two statements range over every current Arrow and every old
whole functional G-quotient correspondence with nonempty ACTUAL
current trace, respectively. It is NOT a bijection assertion between
arbitrarily chosen representatives of quotient point classes. -/
theorem full_reached_original_bridge_correspondence
    (A B : CurrentSource.{u,v,w,t})
    (P : UnaryReduct A.source B.source)
    (transport : ExactTraceTransport A.source B.source P)
    (tp : ExactTraceProduct A.source B.source P)
    (hOriginalOne : ∀ i j : A.Sorts, i = j)
    {r : B.Sorts} (Kroot : Kernel B.source r)
    (b c : Reached B.source Kroot) :
    let C := exactCalculus_of_homogeneous_CCO
      B.source B.homogeneous B.cco
    let Kb := Reached.kernel B.homogeneous C b
    let Kc := Reached.kernel B.homogeneous C c
    let G := original_largest_gate_kernel A B P transport tp b.val Kb
    (∀ R : Arrow B.source Kb Kc,
      ∃ old : Arrow A.source G G,
        ∀ x : B.Point b.val, ∀ y : B.Point c.val,
          old.rel (P.point b.val x)
            ((hOriginalOne (P.parent b.val) (P.parent c.val)).symm ▸
              P.point c.val y) ↔ R.rel x y) ∧
    (∀ old : Arrow A.source G G,
      (∃ x : B.Point b.val, ∃ y : B.Point c.val,
        old.rel (P.point b.val x)
          ((hOriginalOne (P.parent b.val) (P.parent c.val)).symm ▸
            P.point c.val y)) →
      ∃ R : Arrow B.source Kb Kc,
        ∀ x : B.Point b.val, ∀ y : B.Point c.val,
          R.rel x y ↔ old.rel (P.point b.val x)
            ((hOriginalOne (P.parent b.val) (P.parent c.val)).symm ▸
              P.point c.val y)) := by
  dsimp only
  let calculus := exactCalculus_of_homogeneous_CCO
    B.source B.homogeneous B.cco
  let Kb := Reached.kernel B.homogeneous calculus b
  let Kc := Reached.kernel B.homogeneous calculus c
  let G := original_largest_gate_kernel A B P transport tp b.val Kb
  let hSame := hOriginalOne (P.parent b.val) (P.parent c.val)
  have hConnect : Arrow B.source Kb Kc :=
    Reached.connectingArrow B.homogeneous calculus b c
  constructor
  · intro R
    exact current_arrow_original_correspondence_trace
      A B P transport tp hSame Kb Kc R
  · intro old hReal
    have hGateP : ∀ x z : B.Point b.val,
        G.rel (P.point b.val x) (P.point b.val z) ↔
          Kb.rel x z := by
      let F := current_kernel_exact_eq B Kb
      let L := PrefixExactLargestLift.largest
        A B P transport tp b.val F
      have hLift : PrefixExactRestriction.rho A B P transport b.val L = F :=
        (PrefixExactLargestLift.largest_spec
          A B P transport tp b.val F).1
      intro x z
      have h := (PrefixExactRestriction.rho_iff
        A B P transport b.val L x z).symm
      rw [hLift] at h
      exact h
    have hGateQ : ∀ y z : B.Point c.val,
        G.rel (hSame.symm ▸ P.point c.val y)
          (hSame.symm ▸ P.point c.val z) ↔ Kc.rel y z := by
      intro y z
      exact (current_arrow_original_gate_target_trace
        A B P transport tp hSame Kb Kc hConnect y z).symm
    let R : Arrow B.source Kb Kc :=
      original_arrow_trace_to_current_arrow
        A B P transport tp hSame G Kb Kc
        hGateP hGateQ old hReal
    exact ⟨R,fun _ _ => Iff.rfl⟩

/-- The genuine marked SourcePhase selects exactly this entire
reached connected groupoid. The phase parameter is the ACTUAL provider
object, not an extra assumption about a selected generator or a
separately postulated subgroupoid. -/
theorem actual_source_phase_full_bridge_correspondence
    (A B : CurrentSource.{u,v,w,t})
    (P : UnaryReduct A.source B.source)
    (transport : ExactTraceTransport A.source B.source P)
    (tp : ExactTraceProduct A.source B.source P)
    (hOriginalOne : ∀ i j : A.Sorts, i = j)
    {r : B.Sorts} {Kroot : Kernel B.source r}
    (_phase : SourcePhase B.source B.homogeneous
      (exactCalculus_of_homogeneous_CCO
        B.source B.homogeneous B.cco) Kroot)
    (b c : Reached B.source Kroot) :
    let C := exactCalculus_of_homogeneous_CCO
      B.source B.homogeneous B.cco
    let Kb := Reached.kernel B.homogeneous C b
    let Kc := Reached.kernel B.homogeneous C c
    let G := original_largest_gate_kernel A B P transport tp b.val Kb
    (∀ R : Arrow B.source Kb Kc,
      ∃ old : Arrow A.source G G,
        ∀ x : B.Point b.val, ∀ y : B.Point c.val,
          old.rel (P.point b.val x)
            ((hOriginalOne (P.parent b.val) (P.parent c.val)).symm ▸
              P.point c.val y) ↔ R.rel x y) ∧
    (∀ old : Arrow A.source G G,
      (∃ x : B.Point b.val, ∃ y : B.Point c.val,
        old.rel (P.point b.val x)
          ((hOriginalOne (P.parent b.val) (P.parent c.val)).symm ▸
            P.point c.val y)) →
      ∃ R : Arrow B.source Kb Kc,
        ∀ x : B.Point b.val, ∀ y : B.Point c.val,
          R.rel x y ↔ old.rel (P.point b.val x)
            ((hOriginalOne (P.parent b.val) (P.parent c.val)).symm ▸
              P.point c.val y)) :=
  full_reached_original_bridge_correspondence
    A B P transport tp hOriginalOne Kroot b c

end
end CCO.ExactEPGeometry
