import CCO.ExactEPGeometry.OriginalRetainedComparisonTables
import CCO.ExactEPGeometry.NamedTableMotions

/-!
# B062 C103: true finite motions of BOTH retained comparison sources

The same complete owner/colour code is instantiated on the actual next
original-E selected quotient AND the actual retained selected SourcePhase
successor. Each complete-code theorem is discharged from its true palette;
the two actual full homogeneous source groups supply all tuple motions.
Neither direction is a conditional source-homogeneity receiver.
-/

universe u v w t
namespace CCO.ExactEPGeometry
open APCharacter APCharacter.SourceAge APCharacter.Towers
open RigidGroupoid.Geometry FullPhaseLift.BinarySource.MarkedComparison
noncomputable section

variable (A B : CurrentSource.{u,v,w,t})
variable (P : UnaryReduct A.source B.source)
variable (transport : ExactTraceTransport A.source B.source P)
variable (tp : ExactTraceProduct A.source B.source P)
variable (hOne : ∀ i j : A.Sorts, i = j)
variable {r : B.Sorts} (Kroot : Kernel B.source r)
variable (phase : SourcePhase B.source B.homogeneous
  (exactCalculus_of_homogeneous_CCO B.source B.homogeneous B.cco) Kroot)
variable (E : ExactEq A.source (P.parent r))
variable (hE : E ≤ PrefixExactLargestLift.largest A B P transport tp r
  (current_kernel_exact_eq B Kroot))

/-- ALL finite tuple motions of the complete actual quotient table
come from its actual homogeneous source group. -/
theorem originalRetainedQuotientComparisonTable_motions :
    TupleMotions (originalRetainedQuotientComparisonTable A B P transport tp hOne Kroot phase E hE) := by
  let base := P.parent r
  let hBase : ∀ i : A.Sorts, base = i := fun i => hOne base i
  let N := SingleStep.successor B phase
  let R := SingleStep.projection B phase
  let hN := ExactTraceTransport.compose P R transport (canonical_step_exact_transport B phase)
  let QN := originalExactSelectedQuotientCurrentSource A N (P.compose R) hN base hBase E
  exact namedTableMotions_of_completePalette QN.source QN.homogeneous
    (originalRetainedQuotientComparisonTable A B P transport tp hOne Kroot phase E hE)
    (originalRetainedQuotientComparisonTable_palette_iff A B P transport tp hOne Kroot phase E hE)

/-- ALL finite tuple motions of the actual retained SourcePhase
successor table come from that actual marked homogeneous source group. -/
theorem originalRetainedSuccessorComparisonTable_motions :
    TupleMotions (originalRetainedSuccessorComparisonTable A B P transport tp hOne Kroot phase E hE) := by
  let base := P.parent r
  let hBase : ∀ i : A.Sorts, base = i := fun i => hOne base i
  let QB := originalExactSelectedQuotientCurrentSource A B P transport base hBase E
  let φ := originalRetainedActualSelectedPhase A B P transport tp hOne Kroot phase E hE
  let M := SingleStep.successor QB φ
  exact namedTableMotions_of_completePalette M.source M.homogeneous
    (originalRetainedSuccessorComparisonTable A B P transport tp hOne Kroot phase E hE)
    (originalRetainedSuccessorComparisonTable_palette_iff A B P transport tp hOne Kroot phase E hE)

end
end CCO.ExactEPGeometry
