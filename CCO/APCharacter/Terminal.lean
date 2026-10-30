import CCO.APCharacter.SourceAge.SingleStep
import CCO.APCharacter.Towers.HistoryCoherence

/-! Actual AP-only finite character terminalisation. Every successor is
constructed from the CURRENT source and its actual finite interval; the
principal exports have no split, rank, completion, or Fraisse provider input.
The finite history retains literal original reduct projections and every
reasonable/reduct-surjective/precompact unary expansion certificate. -/
universe u v w t
namespace CCO.APCharacter
open Towers RigidGroupoid.Geometry
noncomputable section

/-- The full CURRENT-source theorem, including a finite actual old-reduct
projection tower and the actual composed finite-age unary expansion. -/
theorem finite_character_elimination (initial : CurrentSource.{u,v,w,t}) :
    ∃ terminal : CurrentSource.{u,v,w,t},
      ∃ history : History (fun A B => Nonempty (CurrentSource.ActualStep A B)) initial terminal,
        terminal.Terminal ∧ history.length + terminal.potential ≤ initial.potential ∧
        ∃ reduct : UnaryReduct initial.source terminal.source,
          ∃ unary : UnaryTransition initial.finiteAge terminal.finiteAge,
            unary.forget = reduct.forget :=
  CurrentSource.actual_terminalisation_coherent SourceAge.SingleStep.actual_progress initial

variable {ι : Type u} {X : ι → Type v} (S : AtomicSource.{u,v,w} ι X)
variable {G : Type t} [Group G] [∀ i, MulAction G (X i)]
variable (H : HomogeneousSource S G) (cco : SemanticCCO.{u,v,max u v,w} S)
variable (countable : ∀ i, Countable (X i))

def initialSource : CurrentSource.{u,v,w,t} where
  Sorts := ι
  Point := X
  source := S
  G := G
  group := inferInstance
  action := inferInstance
  homogeneous := H
  countable := countable
  cco := cco

/-- The original-source form of the selected finite AP-only character
elimination theorem. Countability is the intended old-source hypothesis;
finite and empty carriers are allowed. No SAP is added or concluded. -/
theorem ap_finite_character_elimination :
    ∃ terminal : CurrentSource.{u,v,w,t},
      ∃ history : History (fun A B => Nonempty (CurrentSource.ActualStep A B))
          (initialSource S H cco countable) terminal,
        terminal.Terminal ∧
        history.length + terminal.potential ≤ (initialSource S H cco countable).potential ∧
        ∃ reduct : UnaryReduct S terminal.source,
          ∃ unary : UnaryTransition (initialSource S H cco countable).finiteAge terminal.finiteAge,
            unary.forget = reduct.forget :=
  finite_character_elimination (initialSource S H cco countable)

/-- An available finite relative interval gives a genuine first safe split,
then the SAME actual current-source construction eliminates all remaining
finite intervals. This does not invoke any later SAP or Ramsey theorem. -/
theorem ep_ap_safe_splitting
    (h : (initialSource S H cco countable).Obstruction) :
    ∃ next : CurrentSource.{u,v,w,t},
      Nonempty (CurrentSource.ActualStep (initialSource S H cco countable) next) ∧
      ∃ terminal : CurrentSource.{u,v,w,t},
        ∃ history : History (fun A B => Nonempty (CurrentSource.ActualStep A B)) next terminal,
          terminal.Terminal ∧ history.length + terminal.potential ≤ next.potential ∧
          ∃ reduct : UnaryReduct next.source terminal.source,
            ∃ unary : UnaryTransition next.finiteAge terminal.finiteAge,
              unary.forget = reduct.forget := by
  obtain ⟨next,hs⟩ := SourceAge.SingleStep.actual_progress (initialSource S H cco countable) h
  obtain ⟨terminal,history,ht,hbound,hred,hunary,heq⟩ := finite_character_elimination next
  exact ⟨next,hs,terminal,history,ht,hbound,hred,hunary,heq⟩

end
end CCO.APCharacter
