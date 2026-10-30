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

/-- One ACTUAL chosen original parity gate and the exact successor built
from its detecting character. The original Y/O and literal odd-word
relations remain recoverable at every current stage. -/
structure SelectedStep (A B : CurrentSource.{u,v,w,t}) where
  sort : A.base.Sorts
  point : A.base.Point sort
  atom : A.base.source.Atom sort sort
  parity : Full.ParityGateData A.base.source A.base.homogeneous atom point
  target : B = A.successor (parity.phase A.base.cco)

namespace SelectedStep
variable {A B : CurrentSource.{u,v,w,t}} (s : SelectedStep A B)

abbrev kernel := s.parity.kernel
abbrev phase := s.parity.phase A.base.cco

def toActualStep : CurrentSource.ActualStep A B :=
  Eq.mp (congrArg (fun C => CurrentSource.ActualStep A C) s.target.symm)
    (A.actualStep s.phase)

theorem potential_lt (step : SelectedStep A B) : B.potential < A.potential :=
  CurrentSource.ActualStep.potential_lt step.toActualStep

theorem original_even (x y : A.base.Point s.sort)
    (h : ParityHasse.Original.evenColourEq A.base.source A.base.homogeneous s.atom x y) :
    Readout.marking A.base s.phase ⟨s.sort,y⟩ =
      Readout.marking A.base s.phase ⟨s.sort,x⟩ :=
  Readout.original_even A.base s.parity x y h

theorem original_odd (x y : A.base.Point s.sort)
    (h : ParityHasse.Relative.odd
      (ParityHasse.Original.evenColourEq A.base.source A.base.homogeneous s.atom).val
      (ParityHasse.Original.connectivityColourEq A.base.source A.base.homogeneous s.atom).val x y) :
    Readout.marking A.base s.phase ⟨s.sort,y⟩ =
      Readout.marking A.base s.phase ⟨s.sort,x⟩ + 1 :=
  Readout.original_odd A.base s.parity x y h

theorem original_odd_walk (x y : A.base.Point s.sort)
    (h : ParityHasse.Original.OddWalk (A.base.source.atomRel s.atom) x y) :
    Readout.marking A.base s.phase ⟨s.sort,y⟩ =
      Readout.marking A.base s.phase ⟨s.sort,x⟩ + 1 :=
  Readout.original_odd_walk A.base s.parity x y h

end SelectedStep

abbrev SelectedNext (A B : CurrentSource.{u,v,w,t}) := Nonempty (SelectedStep A B)

/-- Select original Y/O from the actual CURRENT finite interval. The
same concrete parity gate supplies the phase AND the next actual source. -/
theorem selected_progress (A : CurrentSource.{u,v,w,t}) (h : A.Obstruction) :
    ∃ B : CurrentSource.{u,v,w,t}, SelectedNext A B := by
  obtain ⟨i,E,F,a,hEF,hfin⟩ := h
  letI := hfin
  obtain ⟨c,⟨D⟩,_,_⟩ := Full.exists_parity_gate A.base.source A.base.homogeneous
    A.base.cco A.sap E F hEF a
  exact ⟨A.successor (D.phase A.base.cco),⟨⟨i,a,c,D,rfl⟩⟩⟩

/-- Source-facing selected split. Its witness retains ORIGINAL Y, O and
OddWalk, with all bit equations on the SAME successor identification. -/
theorem selected_safe_exact_split (A : CurrentSource.{u,v,w,t}) (h : A.Obstruction) :
    ∃ B : CurrentSource.{u,v,w,t}, Nonempty (SelectedStep A B) :=
  selected_progress A h

/-- Compatibility form: even this older signature now uses the concrete
selected original parity gate, rather than an unrelated phase existential. -/
theorem safe_exact_split (A : CurrentSource.{u,v,w,t}) (h : A.Obstruction) :
    ∃ (i : A.base.Sorts) (K : Kernel A.base.source i)
      (P : SourcePhase A.base.source A.base.homogeneous
        (exactCalculus_of_homogeneous_CCO A.base.source A.base.homogeneous A.base.cco) K),
      Nonempty (CurrentSource.ActualStep A (A.successor P)) ∧
      (A.successor P).potential < A.potential ∧
      (∀ (b : Reached A.base.source K) (x y : A.base.Point b.val),
        (P.atSort b).rel x y →
        Readout.marking A.base P ⟨b.val,y⟩ = Readout.marking A.base P ⟨b.val,x⟩ + 1) := by
  obtain ⟨B,⟨s⟩⟩ := selected_progress A h
  exact ⟨s.sort,s.kernel,s.phase,⟨A.actualStep s.phase⟩,A.actual_potential_drop s.phase,
    fun b x y hxy => Readout.transported_odd_orientation A.base s.phase b x y hxy⟩

def selectedHistoryToActual {A B : CurrentSource.{u,v,w,t}}
    (h : History SelectedNext A B) : History CurrentSource.Next A B := by
  induction h with
  | nil A => exact .nil A
  | cons hs tail ih => exact .cons ⟨(Classical.choice hs).toActualStep⟩ ih

theorem selectedHistoryToActual_length {A B : CurrentSource.{u,v,w,t}}
    (h : History SelectedNext A B) : (selectedHistoryToActual h).length = h.length := by
  induction h with
  | nil => rfl
  | cons hs tail ih => exact congrArg (fun n => n+1) ih

/-- Every stage of this ACTUAL history retains the chosen ORIGINAL
parity layer and the same selected split. No source-stage callback remains. -/
theorem finite_cover_elimination_selected (initial : CurrentSource.{u,v,w,t}) :
    ∃ terminal : CurrentSource.{u,v,w,t},
      ∃ history : History SelectedNext initial terminal,
        terminal.Terminal ∧ history.length + terminal.potential ≤ initial.potential ∧
        ∃ reduct : UnaryReduct initial.base.source terminal.base.source,
          ∃ unary : UnaryTransition initial.base.finiteAge terminal.base.finiteAge,
            unary.forget = reduct.forget := by
  let Next : CurrentSource.{u,v,w,t} → CurrentSource.{u,v,w,t} → Prop := SelectedNext
  obtain ⟨terminal,h,ht,hbound⟩ := eliminate_obstructions Next CurrentSource.potential
    CurrentSource.Obstruction selected_progress
    (fun hs => (Classical.choice hs).potential_lt) initial
  exact ⟨terminal,h,ht,hbound,CurrentSource.historyReduct (selectedHistoryToActual h),
    CurrentSource.historyTransition (selectedHistoryToActual h),rfl⟩

/-- The compatibility export forgets only selected-gate metadata. Its
underlying history and composite reduct are the SAME selected construction. -/
theorem finite_cover_elimination (initial : CurrentSource.{u,v,w,t}) :
    ∃ terminal : CurrentSource.{u,v,w,t},
      ∃ history : History CurrentSource.Next initial terminal,
        terminal.Terminal ∧ history.length + terminal.potential ≤ initial.potential ∧
        ∃ reduct : UnaryReduct initial.base.source terminal.base.source,
          ∃ unary : UnaryTransition initial.base.finiteAge terminal.base.finiteAge,
            unary.forget = reduct.forget := by
  obtain ⟨terminal,h,ht,hbound,red,unary,heq⟩ := finite_cover_elimination_selected initial
  refine ⟨terminal,selectedHistoryToActual h,ht,?_,red,unary,heq⟩
  rw [selectedHistoryToActual_length]
  exact hbound

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

/-- The principal ORIGINAL-source terminal export retains the selected
parity gate at EVERY intermediate stage, with its actual old Y/O readout. -/
theorem original_selected_finite_cover_elimination :
    ∃ terminal : CurrentSource.{u,v,w,t},
      ∃ history : History SelectedNext (initialSource S H sap cco countable) terminal,
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
    finite_cover_elimination_selected (initialSource S H sap cco countable)
  exact ⟨terminal,h,ht,hbound,terminal.sap,terminal.semanticCCO,
    fun V D hs => terminal.full_triangle_age D hs,
    fun i E F hEF a => terminal.terminal_cover_infinite ht E F hEF a,
    red,unary,heq⟩

end
end CCO.PairSafeSplit.Terminal
