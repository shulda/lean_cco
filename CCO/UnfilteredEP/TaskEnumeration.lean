import CCO.UnfilteredEP.HierarchyCharting
import Mathlib.Data.Fintype.Sort
import Mathlib.Data.Prod.Lex

/-! One fixed coarse-first enumeration of the ACTUAL transition-orbit
cuts. Choices concern only the finite signature, never an expanded host. -/

universe u v w
namespace CCO.UnfilteredEP
open CCO.CloneTupleGeometry CCO.APRamseyReadout
noncomputable section
variable (B : OwnerStage.{u,v,w}) (ht : B.Terminal)

instance cutOrbit_finite : Finite (CutOrbit B ht) := by
  apply Finite.of_surjective (fun D : HiddenCut B =>
    (NamedCutPath.ambientPaths (B := B) (ht := ht)).orbit D)
  intro q
  induction q using Quotient.inductionOn with | _ D => exact ⟨D,rfl⟩

def taskCount : Nat := Nat.card (CutOrbit B ht)
def taskRank (r : CutOrbit B ht) : Nat := hiddenCutRank B (cutRepresentative B ht r).val

def taskCode : CutOrbit B ht ≃ Fin (taskCount B ht) := by
  let _ := Fintype.ofFinite (CutOrbit B ht)
  exact Fintype.equivFinOfCardEq Nat.card_eq_fintype_card.symm

/-- Equal-rank tasks are broken by one fixed finite signature code. -/
@[instance_reducible] def taskOrder : LinearOrder (CutOrbit B ht) :=
  LinearOrder.lift' (fun r => toLex (taskRank B ht r,taskCode B ht r)) (by
    intro r s h
    apply (taskCode B ht).injective
    exact congrArg (fun p : Nat ×ₗ Fin (taskCount B ht) => (ofLex p).2) h)

def taskEnumeration : Fin (taskCount B ht) ≃ CutOrbit B ht := by
  let _ := Fintype.ofFinite (CutOrbit B ht)
  let _ := taskOrder B ht
  exact (monoEquivOfFin (CutOrbit B ht) Nat.card_eq_fintype_card.symm).toEquiv

/-- All strict coarser tasks occur before any finer task. -/
theorem taskEnumeration_rank_mono {i j : Fin (taskCount B ht)} (hij : i ≤ j) :
    taskRank B ht (taskEnumeration B ht i) ≤ taskRank B ht (taskEnumeration B ht j) := by
  let _ := Fintype.ofFinite (CutOrbit B ht)
  let _ := taskOrder B ht
  let e : Fin (taskCount B ht) ≃o CutOrbit B ht :=
    monoEquivOfFin (CutOrbit B ht) Nat.card_eq_fintype_card.symm
  have he := e.monotone hij
  change toLex (taskRank B ht (e i),taskCode B ht (e i)) ≤
    toLex (taskRank B ht (e j),taskCode B ht (e j)) at he
  exact Prod.Lex.monotone_fst _ _ he

/-- Literal representative cut at a finite task position. -/
abbrev taskCut (i : Fin (taskCount B ht)) : HiddenCut B :=
  (cutRepresentative B ht (taskEnumeration B ht i)).val

end
end CCO.UnfilteredEP
