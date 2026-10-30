import CCO.FullPhaseLift.Tower.Selected
import CCO.FullPhaseLift.Canonical.FullOrbitals
import CCO.FullPhaseLift.BinarySource.FullSAP
import CCO.APCharacter.Terminal
import Lean.Elab.Tactic.Omega

/-! The principal finite FULL selected tower. Actual progress is proved
in Selected; no next-source, marked-limit, pair-comparison or interface
provider remains in this elimination theorem. -/
universe m
namespace CCO.FullPhaseLift.Tower
open Canonical APCharacter APCharacter.Towers ParityHasse.Original
noncomputable section
variable {M : Type m} [Countable M]

/-- Compose the SAME all-arity/global-carrier reducts retained by the
actual selected full steps. No separately chosen reduct replaces them. -/
def historyReduct {A B : CurrentSource M} (h : History Next A B) : FullReduct A.table B.table := by
  induction h with
  | nil A => exact FullReduct.identity A.table
  | cons hs tail ih => exact (Classical.choice hs).reduct.compose ih

def historyTransition {A B : CurrentSource M} (h : History Next A B) :
    UnaryTransition A.finiteAge B.finiteAge :=
  (historyReduct h).transition A.homogeneous

theorem history_forget_eq {A B : CurrentSource M} (h : History Next A B) :
    (historyTransition h).forget = (historyReduct h).forget := rfl

theorem history_language_size {A B : CurrentSource M} (h : History Next A B) :
    B.language.size = A.language.size + h.length := by
  induction h with
  | nil A => simp only [History.length, Nat.add_zero]
  | @cons A B C hs tail ih =>
    have he := (Classical.choice hs).language_size
    change C.language.size = A.language.size + (tail.length+1)
    omega

namespace CurrentSource

theorem full_sap (A : CurrentSource M) : (toRelational A.table).AgeSAP :=
  BinarySource.actual_full_ageSAP A.table A.symmetric (A.normal.to_strict A.table A.symmetric) A.sap

/-- Actual FULL automorphism invariance and canonical pair invariance
have identical equivalence posets and relative classes, including logical Id. -/
theorem terminal_full_cover_infinite (A : CurrentSource M) (ht : A.Terminal)
    (i : UnaryName A.table) (E F : FullInvariantEq A.table i) (hEF : E ⋖ F)
    (a : Carrier A.table i) : Infinite (RelativeClass E.val F.val a) := by
  let e := fullInvariantOrderIso A.table A.homogeneous A.symmetric i
  have hcover : e E ⋖ e F := by
    refine ⟨e.strictMono hEF.lt,?_⟩
    intro C hEC hCF
    have hl : E < e.symm C := by simpa only [e.symm_apply_apply] using e.symm.strictMono hEC
    have hr : e.symm C < F := by simpa only [e.symm_apply_apply] using e.symm.strictMono hCF
    exact hEF.2 hl hr
  exact A.pair.terminal_cover_infinite ht (e E) (e F) hcover a

end CurrentSource

/-- Finite full-language elimination with an ACTUAL selected full
history. Every node is a genuine full homogeneous source with the exact
raw interface, SAP/CCO pair source and finite canonical signature. -/
theorem full_language_elimination (initial : CurrentSource M) :
    ∃ terminal : CurrentSource M, ∃ history : History Next initial terminal,
      terminal.Terminal ∧ history.length + terminal.potential ≤ initial.potential ∧
      terminal.language.size = initial.language.size + history.length ∧
      (toRelational terminal.table).AgeSAP ∧
      (∀ (i : UnaryName terminal.table) (E F : FullInvariantEq terminal.table i),
        E ⋖ F → ∀ a : Carrier terminal.table i, Infinite (RelativeClass E.val F.val a)) ∧
      ∃ reduct : FullReduct initial.table terminal.table,
        ∃ unary : UnaryTransition initial.finiteAge terminal.finiteAge,
          unary.forget = reduct.forget := by
  let Next : CurrentSource M → CurrentSource M → Prop := Tower.Next
  obtain ⟨terminal,h,ht,hbound⟩ := eliminate_obstructions Next CurrentSource.potential
    CurrentSource.Obstruction actual_progress (fun hs => (Classical.choice hs).potential_lt) initial
  exact ⟨terminal,h,ht,hbound,history_language_size h,terminal.full_sap,
    fun i E F hEF a => terminal.terminal_full_cover_infinite ht i E F hEF a,
    historyReduct h,historyTransition h,rfl⟩

end
end CCO.FullPhaseLift.Tower
