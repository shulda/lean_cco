import CCO.FullPhaseLift.BinarySource.ActualContext
import CCO.FullPhaseLift.Full.ActualShadow

/-! Source-facing C07–C08 use the EXACT certified canonical-shadow A03.
The strict semantic interface used internally is DERIVED by the proved
actual-shadow constructor, without pair homogeneity, SAP or CCO premises. -/

universe u z
namespace CCO.FullPhaseLift.BinarySource
open Canonical
noncomputable section
variable {L : Signature} {M : Type u} [Countable M]
variable (U : BoolTable L M) (hsym : SameSortSymmetric U)
variable (hom : (toRelational U).Homogeneous)
variable (normal : Full.Shadow.SupportNormal U hsym)

include hom normal in
theorem certified_binary_homogeneous :
    HomogeneousSource (source U hsym) (TerminalPowers.FullAut (source U hsym)) :=
  actual_binary_homogeneous U hsym hom (normal.to_strict U hsym)

include hom normal in
theorem certified_full_triangle_age (cco : SemanticCCO.{0,u,z,0} (source U hsym))
    {V : Type z} (D : CompleteDiagram (S := source U hsym) V)
    (small : D.SmallRealizable) : ∃ f : DiagramHom D.diagram, f.IsInjective :=
  actual_full_triangle_age U hsym hom (normal.to_strict U hsym) cco D small

def certifiedPairContext (sap : AgeSAP (source U hsym))
    (cco : SemanticCCO.{0,u,u,0} (source U hsym)) :
    PairSafeSplit.Terminal.CurrentSource.{0,u,0,u} :=
  actualPairContext U hsym hom (normal.to_strict U hsym) sap cco

end
end CCO.FullPhaseLift.BinarySource
