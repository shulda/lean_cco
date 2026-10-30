import CCO.PairSafeSplit.Terminal.Successor
import CCO.APCharacter.Terminal

/-! Source results thm:safe-exact-split and thm:finite-cover-elimination.
Every actual CURRENT stage is homogeneous, SAP, semantic CCO and FULL
triangle-defined. The progress theorem is proved above, not a caller input. -/

universe u v w t z
namespace CCO.PairSafeSplit.Terminal
open APCharacter APCharacter.Towers APCharacter.SourceAge
open RigidGroupoid.Geometry
noncomputable section

/-- A finite relative interval supplies an ACTUAL detecting maximal
character split and its literal reasonable precompact unary reduct. -/
theorem safe_exact_split (A : CurrentSource.{u,v,w,t}) (h : A.Obstruction) :
    ∃ (i : A.base.Sorts) (K : Kernel A.base.source i)
      (P : SourcePhase A.base.source A.base.homogeneous
        (exactCalculus_of_homogeneous_CCO A.base.source A.base.homogeneous A.base.cco) K),
      Nonempty (CurrentSource.ActualStep A (A.successor P)) ∧
      (A.successor P).potential < A.potential ∧
      (∀ (b : Reached A.base.source K) (x y : A.base.Point b.val),
        (P.atSort b).rel x y →
        Readout.marking A.base P ⟨b.val,y⟩ = Readout.marking A.base P ⟨b.val,x⟩ + 1) := by
  obtain ⟨i,K,⟨P⟩⟩ := A.base.phase_of_obstruction h
  exact ⟨i,K,P,⟨A.actualStep P⟩,A.actual_potential_drop P,
    fun b x y hxy => Readout.transported_odd_orientation A.base P b x y hxy⟩

/-- Finite CURRENT-source terminalisation with SAP at every history node.
The SAME composite point/sort/atom projection carries the actual reasonable,
reduct-surjective and precompact finite-age expansion functor. -/
theorem finite_cover_elimination (initial : CurrentSource.{u,v,w,t}) :
    ∃ terminal : CurrentSource.{u,v,w,t},
      ∃ history : History CurrentSource.Next initial terminal,
        terminal.Terminal ∧ history.length + terminal.potential ≤ initial.potential ∧
        ∃ reduct : UnaryReduct initial.base.source terminal.base.source,
          ∃ unary : UnaryTransition initial.base.finiteAge terminal.base.finiteAge,
            unary.forget = reduct.forget := by
  let Next : CurrentSource.{u,v,w,t} → CurrentSource.{u,v,w,t} → Prop := CurrentSource.Next
  obtain ⟨terminal,h,ht,hbound⟩ := eliminate_obstructions Next CurrentSource.potential
    CurrentSource.Obstruction CurrentSource.actual_progress
    (fun hs => (Classical.choice hs).potential_lt) initial
  exact ⟨terminal,h,ht,hbound,CurrentSource.historyReduct h,
    CurrentSource.historyTransition h,rfl⟩

variable {ι : Type u} {X : ι → Type v} (S : AtomicSource.{u,v,w} ι X)
variable {G : Type t} [Group G] [∀ i, MulAction G (X i)]
variable (H : HomogeneousSource S G) (sap : AgeSAP S)
variable (cco : SemanticCCO.{u,v,max u v,w} S) (countable : ∀ i, Countable (X i))

def initialSource : CurrentSource.{u,v,w,t} where
  base := APCharacter.initialSource S H cco countable
  sap := sap

/-- Original-source form. There is no split/completion/SAP/rank/Fraïssé
provider for later stages, nor any later Ramsey or full-language premise. -/
theorem original_finite_cover_elimination :
    ∃ terminal : CurrentSource.{u,v,w,t},
      ∃ history : History CurrentSource.Next (initialSource S H sap cco countable) terminal,
        terminal.Terminal ∧
        history.length + terminal.potential ≤ (initialSource S H sap cco countable).potential ∧
        AgeSAP terminal.base.source ∧ SemanticCCO.{u,v,z,w} terminal.base.source ∧
        (∀ (V : Type z) (D : CompleteDiagram (S := terminal.base.source) V),
          D.SmallRealizable → ∃ f : DiagramHom D.diagram, f.IsInjective) ∧
        (∀ (i : terminal.base.Sorts) (E F : ParityHasse.Original.ColourEq terminal.base.source i),
          E ⋖ F → ∀ a : terminal.base.Point i,
            Infinite (ParityHasse.Original.RelativeClass E.val F.val a)) ∧
        ∃ reduct : UnaryReduct S terminal.base.source,
          ∃ unary : UnaryTransition (initialSource S H sap cco countable).base.finiteAge
              terminal.base.finiteAge,
            unary.forget = reduct.forget := by
  obtain ⟨terminal,h,ht,hbound,red,unary,heq⟩ :=
    finite_cover_elimination (initialSource S H sap cco countable)
  exact ⟨terminal,h,ht,hbound,terminal.sap,terminal.semanticCCO,
    fun V D hs => terminal.full_triangle_age D hs,
    fun i E F hEF a => terminal.terminal_cover_infinite ht E F hEF a,
    red,unary,heq⟩

end
end CCO.PairSafeSplit.Terminal
