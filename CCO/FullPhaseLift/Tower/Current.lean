import CCO.FullPhaseLift.Marked.OnOldCarrier
import CCO.FullPhaseLift.BinarySource.ActualContext
import CCO.FullPhaseLift.Tower.FiniteAgeReduct

/-! Actual full CURRENT prefixes. A later prefix is constructed from the
previous full Fraisse class; none of the fields is a next-stage provider.
Every prefix keeps the SAME original carrier and a finite full signature. -/
universe m
namespace CCO.FullPhaseLift.Tower
open Canonical APCharacter
noncomputable section

structure CurrentSource (M : Type m) where
  language : Signature
  table : BoolTable language M
  homogeneous : (toRelational table).Homogeneous
  symmetric : SameSortSymmetric table
  normal : Full.Shadow.SupportNormal table symmetric
  sap : AgeSAP (source table symmetric)
  cco : SemanticCCO.{0,m,m,0} (source table symmetric)

namespace CurrentSource
variable {M : Type m} [Countable M]

def pair (A : CurrentSource M) : PairSafeSplit.Terminal.CurrentSource.{0,m,0,m} :=
  BinarySource.actualPairContext A.table A.symmetric A.homogeneous
    (A.normal.to_strict A.table A.symmetric) A.sap A.cco

abbrev potential (A : CurrentSource M) := A.pair.potential
abbrev Obstruction (A : CurrentSource M) := A.pair.Obstruction
abbrev Terminal (A : CurrentSource M) := A.pair.Terminal

def finiteAge (A : CurrentSource M) : Towers.UnaryAge :=
  ⟨Marked.OldChart A.table,Marked.oldCategory A.table⟩

/-- Every finite named full prefix has its literal old FULL age; the
separate pair homogeneity proof is derived from raw A03 at this prefix. -/
theorem pair_source (A : CurrentSource M) : A.pair.base.source = source A.table A.symmetric := rfl

theorem pair_homogeneous (A : CurrentSource M) :
    HomogeneousSource (source A.table A.symmetric)
      (TerminalPowers.FullAut (source A.table A.symmetric)) :=
  Full.Shadow.actual_binary_homogeneous A.table A.symmetric A.homogeneous A.normal

end CurrentSource
end
end CCO.FullPhaseLift.Tower
