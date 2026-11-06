import CCO.ExactEPGeometry.OriginalGateAllLabels
import CCO.ExactEPGeometry.CertifiedOriginalKernel

/-!
# B062 C61: selected source-certified original old gate preserves its next label

A genuine `CertifiedGateTower.GateChoice` retains the EXACT current
MaximalGate M, current source Phase obtained from that SAME M, and the
literal accepted next homogeneous character source. Its original full
RAW-exact gate is the ALREADY PROVED greatest original lift of M.kernel.

Here a real original exact E under that gate is shown to preserve the
actual new child bit of every CURRENT parent sort, both active and
inactive, using the source theorem for the full Reached groupoid.
This is not a lemma about arbitrary guessed gates or arbitrary
unary refinements. ONE-original-sort hypothesis is explicit.
-/

universe u v w t

namespace CCO.ExactEPGeometry

open APCharacter
open APCharacter.SourceAge
open APCharacter.Towers
open CCO.ParityHasse.Original
open CCO.ExactEPGeometry.CertifiedGateTower
open RigidGroupoid.Geometry

noncomputable section

/-- A genuine GateChoice, not a newly chosen phase, preserves the next
child label of all old E-related points in the SAME current parent
sort as soon as E lies below the actually selected greatest ORIGINAL
RAW-exact gate. The fixed source has precisely ONE old sort. -/
theorem certified_gatechoice_preserves_next_child_tag
    (original : CurrentSource.{u,v,w,t})
    (s : CertifiedGateTower.ExactPrefix original)
    (choice : CertifiedGateTower.GateChoice s)
    (hOne : ∀ i j : original.Sorts, i = j)
    (E : ExactEq original.source (s.reduct.parent choice.p))
    (hE : E ≤ PrefixExactLargestLift.largest
      original s.current s.reduct s.transport s.product choice.p
      (⟨choice.M.kernel,choice.M.maximal.1.1⟩ :
        ExactEq s.current.source choice.p))
    (i : s.current.Sorts) (x y : s.current.Point i)
    (hxy : E
      ((hOne (s.reduct.parent choice.p) (s.reduct.parent i)).symm ▸
        s.reduct.point i x)
      ((hOne (s.reduct.parent choice.p) (s.reduct.parent i)).symm ▸
        s.reduct.point i y)) :
    UnarySource.tag (SingleStep.identification s.current choice.phase) i x =
      UnarySource.tag (SingleStep.identification s.current choice.phase) i y := by
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
    intro a b
    exact Iff.rfl
  have hE' : E ≤ PrefixExactLargestLift.largest
      original s.current s.reduct s.transport s.product choice.p
        (current_kernel_exact_eq s.current K) := by
    simpa only [hF] using hE
  exact original_below_largest_preserves_all_next_child
    original s.current s.reduct s.transport s.product
    hOne K choice.phase E hE' i x y hxy

end
end CCO.ExactEPGeometry
