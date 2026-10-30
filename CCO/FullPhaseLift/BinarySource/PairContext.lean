import CCO.FullPhaseLift.BinarySource.AtomicHomogeneity
import CCO.PairSafeSplit.Terminal.Current

/-! C08: actual pair context for the accepted safe-split construction.
The binary homogeneous action is derived by finite extension/back-and-forth;
the FULL triangle age then follows from accepted AP plus homomorphic CCO. -/

universe u v w z
namespace CCO.FullPhaseLift.BinarySource
open APCharacter.SourceAge
open TerminalPowers
noncomputable section
variable {ι : Type u} {X : ι → Type v} (S : AtomicSource.{u,v,w} ι X)
variable [Countable (Sigma X)]
variable (ext : FiniteExtension (sourceTable S) (sourceTable S))
include ext

/-- No full-old SAP or triangle-completion oracle is supplied. The
homogeneous action here is the newly proved actual binary action. -/
theorem full_triangle_age (cco : SemanticCCO.{u,v,z,w} S)
    {V : Type z} (D : CompleteDiagram (S := S) V) (hsmall : D.SmallRealizable) :
    ∃ f : DiagramHom D.diagram, f.IsInjective :=
  D.triangleFullness_of_homogeneous_CCO (homogeneous_of_finiteExtension S ext) cco hsmall

/-- The same actual binary carrier/source now meets the accepted B047
current-source context. Its SAP field is precisely the pair-age premise. -/
def pairContext (sap : AgeSAP S) (cco : SemanticCCO.{u,v,max u v,w} S) :
    PairSafeSplit.Terminal.CurrentSource.{u,v,w,max u v} where
  base := {
    Sorts := ι
    Point := X
    source := S
    G := FullAut S
    group := inferInstance
    action := inferInstance
    homogeneous := homogeneous_of_finiteExtension S ext
    countable := fun i => Function.Injective.countable (f := Sigma.mk i) (by
      intro x y h
      simpa only [Sigma.mk.injEq,heq_eq_eq,true_and] using h)
    cco := cco }
  sap := sap

theorem pairContext_source (sap : AgeSAP S) (cco : SemanticCCO.{u,v,max u v,w} S) :
    (pairContext S ext sap cco).base.source = S := rfl

end
end CCO.FullPhaseLift.BinarySource
