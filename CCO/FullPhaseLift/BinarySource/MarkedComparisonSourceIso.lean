import CCO.FullPhaseLift.BinarySource.MarkedComparison
import CCO.FullPhaseLift.Full.SourceIso

/-! The actual typed canonical binary source of the full marked prefix is
isomorphic to the selected B047 successor, including real optional
colours. All comparison and source-name providers are instantiated. -/

universe m t
namespace CCO.FullPhaseLift.BinarySource.MarkedComparison
open Canonical APCharacter RigidGroupoid.Geometry
open APCharacter.SourceAge.UnarySource
noncomputable section
variable {L : Signature} {M : Type m} [Countable M] (U : BoolTable L M) (hsym : SameSortSymmetric U)
variable {G : Type t} [Group G] [∀ i, MulAction G (Canonical.Carrier U i)]
variable {H : HomogeneousSource (Canonical.source U hsym) G}
variable {C : ExactCalculus (Canonical.source U hsym)} {a : UnaryName U}
variable {K : Kernel (Canonical.source U hsym) a}
variable (P : SourcePhase (Canonical.source U hsym) H C K)
variable (cco : SemanticCCO.{0,m,m,0} (Canonical.source U hsym))
variable (I : Identification (Canonical.source U hsym) H (P.completion_property cco))
variable (sap : Marked.StrongAmalgamation U (Canonical.source U hsym) (Canonical.pack U) P.masks)
variable (oldIso : Canonical.Iso
  (FullReduct.oldTable U (Canonical.source U hsym) (Canonical.pack U) P.masks sap) U)

def nativeSourceIso (normal : Full.StrictSupportNormal U) :
    Full.SourceIso
      (Canonical.source
        (FullReduct.expandedTable U (Canonical.source U hsym) (Canonical.pack U) P.masks sap)
        (modelSym U hsym P sap oldIso))
      (APCharacter.SourceAge.UnarySource.source I) := by
  let h := comparison_pattern U hsym P cco I sap oldIso normal
  exact Full.SourceIso.of_pattern (Classical.choose h) (Classical.choose_spec h)

end
end CCO.FullPhaseLift.BinarySource.MarkedComparison
