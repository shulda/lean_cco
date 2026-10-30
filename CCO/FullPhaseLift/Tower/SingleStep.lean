import CCO.FullPhaseLift.Tower.Current
import CCO.PairSafeSplit.Terminal.Successor
import CCO.FullPhaseLift.Canonical.Homogeneity
import CCO.FullPhaseLift.Canonical.UnaryExpansion
import CCO.FullPhaseLift.BinarySource.MarkedLimitSAP
import CCO.FullPhaseLift.Full.CanonicalIso
import CCO.FullPhaseLift.Full.SourceInvariants

/-! The concrete FULL realization of one selected actual pair phase.
The entire marked Fraisse model, full old-reduct isomorphism, legal mark,
full SAP and next strict interface are constructed here. -/
universe m
namespace CCO.FullPhaseLift.Tower.SingleStep
open Canonical APCharacter APCharacter.SourceAge RigidGroupoid.Geometry
noncomputable section
variable {M : Type m} [Countable M] (A : CurrentSource M)
variable {i : A.pair.base.Sorts} {K : Kernel A.pair.base.source i}
variable (P : SourcePhase A.pair.base.source A.pair.base.homogeneous
  (exactCalculus_of_homogeneous_CCO A.pair.base.source A.pair.base.homogeneous A.pair.base.cco) K)

abbrev mask := P.masks

def classSAP : Marked.StrongAmalgamation A.table (source A.table A.symmetric)
    (Canonical.pack A.table) P.masks := by
  letI := A.pair.base.countable
  exact Marked.strongAmalgamation A.table A.symmetric P.masks
    (A.normal.to_strict A.table A.symmetric)
    (Marked.actual_pairStrongAmalgamation P A.pair.base.cco A.sap)

abbrev Model := BinarySource.FullReduct.Carrier A.table (source A.table A.symmetric)
  (Canonical.pack A.table) P.masks (classSAP A P)

def nativeTable : BoolTable (Marked.addBit A.language) (Model A P) :=
  BinarySource.FullReduct.expandedTable A.table (source A.table A.symmetric)
    (Canonical.pack A.table) P.masks (classSAP A P)

def oldIso : Canonical.Iso (Marked.oldTable (nativeTable A P)) A.table :=
  (BinarySource.FullReduct.old_full_iso A.table (source A.table A.symmetric)
    (Canonical.pack A.table) P.masks (classSAP A P) A.homogeneous
    (Marked.actualPairFaithful A.table A.symmetric) P.finite_seed_extension).some

def mark : M → Bit :=
  BinarySource.FullReduct.bits A.table (source A.table A.symmetric)
    (Canonical.pack A.table) P.masks (classSAP A P) ∘ (oldIso A P).point.symm

def fullTable : BoolTable (Marked.addBit A.language) M := Marked.table A.table (mark A P)

def fullIso : Canonical.Iso (fullTable A P) (nativeTable A P) :=
  Marked.onOldIso A.table (source A.table A.symmetric) (Canonical.pack A.table)
    P.masks (classSAP A P) (oldIso A P)

theorem native_homogeneous : (toRelational (nativeTable A P)).Homogeneous :=
  Canonical.homogeneous_of_firstOrder (inferInstance :
    (Marked.addBit A.language).firstOrder.Structure (Model A P))
    (Marked.limit_homogeneous A.table (source A.table A.symmetric) (Canonical.pack A.table)
      P.masks (classSAP A P))

theorem full_homogeneous : (toRelational (fullTable A P)).Homogeneous :=
  Canonical.homogeneous_of_iso (fullIso A P).symm (native_homogeneous A P)

theorem native_symmetric : SameSortSymmetric (nativeTable A P) :=
  Canonical.sameSortSymmetric_decoded (nativeTable A P) (oldIso A P) A.symmetric

theorem full_symmetric : SameSortSymmetric (fullTable A P) :=
  Canonical.sameSortSymmetric_marked A.symmetric (mark A P)

theorem native_strict : Full.StrictSupportNormal (nativeTable A P) :=
  Marked.strictSupportNormal A.table A.symmetric P.masks (classSAP A P)
    (A.normal.to_strict A.table A.symmetric) (oldIso A P)

theorem full_strict : Full.StrictSupportNormal (fullTable A P) :=
  Marked.strictSupportNormal_of_iso (fullIso A P) (native_strict A P)

theorem full_sap : (toRelational (fullTable A P)).AgeSAP :=
  BinarySource.MarkedLimitSAP.ageSAP_on_isomorphic_table A.table (source A.table A.symmetric)
    (Canonical.pack A.table) P.masks (classSAP A P) (fullTable A P) (fullIso A P)

theorem global_legal : P.masks.GlobalMarking (mark A P ∘ (Canonical.pack A.table).symm) :=
  Marked.model_global_legal A.table (source A.table A.symmetric) (Canonical.pack A.table)
    P.masks (classSAP A P) (Marked.actualPairFaithful A.table A.symmetric) (oldIso A P)

/-- Every old relation is retained LITERALLY on this same carrier. -/
def reduct : FullReduct A.table (fullTable A P) where
  signature := SignatureReduct.bit A.language
  point := Equiv.refl M
  read := rfl

def transition : Towers.UnaryTransition A.finiteAge
    ⟨Marked.OldChart (fullTable A P),Marked.oldCategory (fullTable A P)⟩ :=
  (reduct A P).transition A.homogeneous

abbrev pairChild := A.pair.successor P

/-- A native whole-model pair comparison induces the SAME comparison
on the receiving full source via its genuine FULL model isomorphism. -/
def comparison
    (native : Full.SourceIso (source (nativeTable A P) (native_symmetric A P))
      (pairChild A P).base.source) :
    Full.SourceIso (source (fullTable A P) (full_symmetric A P)) (pairChild A P).base.source :=
  (Full.canonicalSourceIso (fullIso A P) (full_symmetric A P) (native_symmetric A P)).trans native

/-- Internal assembly from a comparison certificate. The final source
progress theorem constructs this certificate from the actual pair ages. -/
def current
    (e : Full.SourceIso (source (fullTable A P) (full_symmetric A P)) (pairChild A P).base.source) :
    CurrentSource M where
  language := Marked.addBit A.language
  table := fullTable A P
  homogeneous := full_homogeneous A P
  symmetric := full_symmetric A P
  sap := e.ageSAP (pairChild A P).sap
  cco := e.semanticCCO (pairChild A P).base.cco
  normal := Full.Shadow.of_strict_full_homogeneous (fullTable A P) (full_symmetric A P)
    (full_homogeneous A P) (full_strict A P) (e.ageSAP (pairChild A P).sap)
    (semanticCCO_change_universe _ (e.semanticCCO (pairChild A P).base.cco))

theorem potential_eq
    (e : Full.SourceIso (source (fullTable A P) (full_symmetric A P)) (pairChild A P).base.source) :
    (current A P e).potential = (pairChild A P).potential := e.potential_eq

end
end CCO.FullPhaseLift.Tower.SingleStep
