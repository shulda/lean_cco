import CCO.FullPhaseLift.BinarySource.ActualExtension
import CCO.FullPhaseLift.BinarySource.PairContext

/-! C08 actual source discharge: the SAME canonical binary source of the
full old structure meets every accepted B047 source condition. The old
FULL triangle age is derived, never an added source premise. -/

universe u z
namespace CCO.FullPhaseLift.BinarySource
open Canonical Full
noncomputable section
variable {L : Signature} {M : Type u} [Countable M]
variable (U : BoolTable L M) (hsym : SameSortSymmetric U)
variable (hom : (toRelational U).Homogeneous) (normal : SupportNormal U)

include hom normal in
theorem actual_full_triangle_age
    (cco : SemanticCCO.{0,u,z,0} (source U hsym))
    {V : Type z} (D : CompleteDiagram (S := source U hsym) V)
    (small : D.SmallRealizable) : ∃ f : DiagramHom D.diagram, f.IsInjective :=
  D.triangleFullness_of_homogeneous_CCO
    (actual_binary_homogeneous U hsym hom normal) cco small

/-- A01 is old FULL homogeneity, A02 is pair SAP+CCO, A03 is the literal
signed full completion interface. Binary homogeneity and full SAP do not
occur in the input as replacement principal-theorem hypotheses. -/
def actualPairContext (sap : AgeSAP (source U hsym))
    (cco : SemanticCCO.{0,u,u,0} (source U hsym)) :
    PairSafeSplit.Terminal.CurrentSource.{0,u,0,u} := by
  letI : Countable (Sigma (Carrier U)) := (pack U).symm.injective.countable
  exact pairContext (source U hsym)
    (source_finiteExtension U hsym (actual_pair_finiteExtension U hsym hom normal)) sap cco

theorem actualPairContext_source (sap : AgeSAP (source U hsym))
    (cco : SemanticCCO.{0,u,u,0} (source U hsym)) :
    (actualPairContext U hsym hom normal sap cco).base.source = source U hsym := rfl

end
end CCO.FullPhaseLift.BinarySource
