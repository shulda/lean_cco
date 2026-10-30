import CCO.FullPhaseLift.Canonical.Normalization
import CCO.FullPhaseLift.Canonical.NameFormulas
import CCO.FullPhaseLift.Full.Receiving
import CCO.FullPhaseLift.Full.ExpansionHomogeneity
import CCO.FullPhaseLift.Full.DefinitionalReduct
import CCO.FullPhaseLift.Detours.Export
import CCO.FullPhaseLift.Tower.Elimination
import CCO.FullPhaseLift.Equivariance.Marked

/-! B048's two selected source results. The finite FULL tower constructs
EVERY successor from its actual full marked Fraisse model, preserves the
exact raw A03 gate and retains the original selected B047 parity witness.
The original pre-naming language is retained by the same composite full
reduct, including every negative/repeated/nullary relation tuple. -/

universe v
namespace CCO.FullPhaseLift
open Canonical APCharacter APCharacter.Towers ParityHasse.Original
noncomputable section

export Detours (root_free_phase_safe)
export Tower (full_language_elimination)

/-- A01's canonical definitional expansion supplies the actual initial
full prefix. The caller gives ONLY full homogeneity, A02 and exact raw
A03; neither full SAP nor actual binary homogeneity is supplied. -/
def canonicalInitialSource {L : Signature} {M : Type v}
    (T : BoolTable L M) (hsym : SameSortSymmetric T)
    (hom : (toRelational T).Homogeneous)
    (normal : Full.Shadow.SupportNormal (expand T) (sameSortSymmetric_expand hsym))
    (sap : AgeSAP (source (expand T) (sameSortSymmetric_expand hsym)))
    (cco : SemanticCCO.{0,v,v,0} (source (expand T) (sameSortSymmetric_expand hsym))) :
    Tower.CurrentSource M where
  language := expansion L
  table := expand T
  homogeneous := expand_homogeneous T hom
  symmetric := sameSortSymmetric_expand hsym
  normal := normal
  sap := sap
  cco := cco

/-- The source theorem also retains the original PRE-naming full language.
Canonical naming is finite and definitional; every subsequent added symbol
is unary. The original all-arity reduct and its finite-age functor are the
SAME actual composite, not a separately chosen binary comparison. -/
theorem canonical_full_language_elimination {L : Signature} {M : Type v} [Countable M]
    (T : BoolTable L M) (hsym : SameSortSymmetric T)
    (hom : (toRelational T).Homogeneous)
    (normal : Full.Shadow.SupportNormal (expand T) (sameSortSymmetric_expand hsym))
    (sap : AgeSAP (source (expand T) (sameSortSymmetric_expand hsym)))
    (cco : SemanticCCO.{0,v,v,0} (source (expand T) (sameSortSymmetric_expand hsym))) :
    ∃ terminal : Tower.CurrentSource M,
      ∃ history : History Tower.Next (canonicalInitialSource T hsym hom normal sap cco) terminal,
      terminal.Terminal ∧
      history.length + terminal.potential ≤
        (canonicalInitialSource T hsym hom normal sap cco).potential ∧
      terminal.language.size = (expansion L).size + history.length ∧
      (toRelational terminal.table).AgeSAP ∧
      (∀ (i : UnaryName terminal.table) (E F : FullInvariantEq terminal.table i),
        E ⋖ F → ∀ a : Carrier terminal.table i, Infinite (RelativeClass E.val F.val a)) ∧
      ∃ reduct : Tower.FullReduct T terminal.table,
        ∃ unary : UnaryTransition ⟨Marked.OldChart T,Marked.oldCategory T⟩ terminal.finiteAge,
          unary.forget = reduct.forget := by
  let initial := canonicalInitialSource T hsym hom normal sap cco
  obtain ⟨terminal,history,ht,hbound,hsize,hsap,hcovers,reduct,_unary,_hforget⟩ :=
    Tower.full_language_elimination initial
  let originalReduct := (Full.definitionalReduct T).compose reduct
  exact ⟨terminal,history,ht,hbound,hsize,hsap,hcovers,
    originalReduct,originalReduct.transition hom,rfl⟩

end
end CCO.FullPhaseLift
