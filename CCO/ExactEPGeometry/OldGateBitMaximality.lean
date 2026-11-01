import CCO.ExactEPGeometry.ActualGateBitMaximality
import CCO.ExactEPGeometry.CertifiedGateLabelStep

/-!
# B062 C62: actual ORIGINAL exact equivalence bounded by its selected old gate

The genuine old-to-current exact-equivalence restriction `rho_p` is
constructed from the proven two-way RAW exact transport, not from a
hypothetical source map. If the original full-exact E restricts to a
current full-exact equivalence whose pairs have the SAME ACTUAL next
child tag, the odd-arrow maximality theorem shows `rho_p(E)<=K_p`.

The established E1/E2/E3 right adjoint then gives E<=L_p(K_p) in the
actual ORIGINAL RAW-exact lattice. Finally the real GateChoice selected
by the original-gate-certified AP-only tower supplies exactly K_p and
the SAME SourcePhase. Nothing is reselected, and no quotient SAP or
global group action section is used.

The history-level converse still must prove tag compatibility at every
actual earlier step from the final all-label property; this file does
not postulate that implication.
-/

universe u v w t

namespace CCO.ExactEPGeometry

open APCharacter
open APCharacter.SourceAge
open APCharacter.Towers
open CCO.ExactEPGeometry.CertifiedGateTower
open CCO.ParityHasse.Original
open RigidGroupoid.Geometry

noncomputable section

/-- C62 at one ACTUAL original-to-current prefix. Preserving the real
next root label implies an OLD exact bound by the greatest ORIGINAL
RAW-exact preimage of the genuine current maximal gate K. This
uses the proved current odd-source maximality and original exact
right adjoint, rather than asserting the bound as an input. -/
theorem original_exact_preserving_root_next_tag_le_largest
    (A B : CurrentSource.{u,v,w,t})
    (P : UnaryReduct A.source B.source)
    (transport : ExactTraceTransport A.source B.source P)
    (tp : ExactTraceProduct A.source B.source P)
    {p : B.Sorts} (K : Kernel B.source p)
    (phase : SourcePhase B.source B.homogeneous
      (exactCalculus_of_homogeneous_CCO
        B.source B.homogeneous B.cco) K)
    (E : ExactEq A.source (P.parent p))
    (hLabels : ∀ x y : B.Point p,
      E (P.point p x) (P.point p y) →
        UnarySource.tag (SingleStep.identification B phase) p x =
          UnarySource.tag (SingleStep.identification B phase) p y) :
    E ≤ PrefixExactLargestLift.largest A B P transport tp p
      (current_kernel_exact_eq B K) := by
  let F := PrefixExactRestriction.rho A B P transport p E
  have hFLabels : ∀ x y : B.Point p, F x y →
      UnarySource.tag (SingleStep.identification B phase) p x =
        UnarySource.tag (SingleStep.identification B phase) p y := by
    intro x y hxy
    exact hLabels x y
      ((PrefixExactRestriction.rho_iff A B P transport p E x y).mp hxy)
  have hFleK : F ≤ current_kernel_exact_eq B K :=
    current_exact_preserving_phase_label_le_gate
      B K phase F hFLabels
  exact ((PrefixExactLargestLift.largest_spec
    A B P transport tp p (current_kernel_exact_eq B K)).2 E).mp hFleK

/-- The SAME selected GateChoice/M/phase from an actual
`CertifiedGateTower.Step` is used. Any ORIGINAL full-RAW-exact
relation E preserving all of that selected root's actual new child
bits must be below the selected greatest original exact gate.

It does not yet infer preservation of those bits solely from the
final tower label; that is a separate backward history argument. -/
theorem certified_gatechoice_original_exact_label_le_gate
    (original : CurrentSource.{u,v,w,t})
    (s : CertifiedGateTower.ExactPrefix original)
    (choice : CertifiedGateTower.GateChoice s)
    (E : ExactEq original.source (s.reduct.parent choice.p))
    (hLabels : ∀ x y : s.current.Point choice.p,
      E (s.reduct.point choice.p x) (s.reduct.point choice.p y) →
        UnarySource.tag
          (SingleStep.identification s.current choice.phase)
            choice.p x =
        UnarySource.tag
          (SingleStep.identification s.current choice.phase)
            choice.p y) :
    E ≤ PrefixExactLargestLift.largest
      original s.current s.reduct s.transport s.product choice.p
      (⟨choice.M.kernel,choice.M.maximal.1.1⟩ :
        ExactEq s.current.source choice.p) := by
  let K : Kernel s.current.source choice.p :=
    APCharacter.MaximalGate.kernel
      s.current.source s.current.homogeneous
      (evenColourEq s.current.source s.current.homogeneous choice.c)
      (connectivityColourEq s.current.source s.current.homogeneous choice.c)
      choice.M
  have hF :
      current_kernel_exact_eq s.current K =
        (⟨choice.M.kernel,choice.M.maximal.1.1⟩ :
          ExactEq s.current.source choice.p) := by
    apply ExactEq.ext
    intro x y
    exact Iff.rfl
  have hBound :=
    original_exact_preserving_root_next_tag_le_largest
      original s.current s.reduct s.transport s.product
      K choice.phase E hLabels
  simpa only [hF] using hBound

end
end CCO.ExactEPGeometry
