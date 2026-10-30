import CCO.APCharacter.Towers.CurrentSource
import CCO.APCharacter.Towers.ProjectionComposition

/-! The finite-history expansion properties belong to EXACTLY the composite
actual original reduct projection, not to a separately chosen functor. -/
universe u v w t
namespace CCO.APCharacter.Towers.CurrentSource
open CategoryTheory
noncomputable section

def historyUnary {A B : CurrentSource.{u,v,w,t}}
    (h : History (fun A B => Nonempty (ActualStep A B)) A B) :
    UnaryTransition A.finiteAge B.finiteAge :=
  finiteUnaryComposite finiteAge (fun hs => (Classical.choice hs).unary) h

/-- Exact equality of the two constructions along the SAME actual step
history. Every step's projection/functor equality remains visible. -/
theorem history_forget_eq {A B : CurrentSource.{u,v,w,t}}
    (h : History (fun A B => Nonempty (ActualStep A B)) A B) :
    (historyReduct h).forget = (historyUnary h).forget := by
  induction h with
  | nil A => exact UnaryReduct.identity_forget A.source
  | cons hs tail ih =>
    change ((Classical.choice hs).reduct.compose (historyReduct tail)).forget =
      (historyUnary tail).forget ⋙ (Classical.choice hs).unary.forget
    rw [UnaryReduct.compose_forget,ih,← (Classical.choice hs).forget_eq]
    rfl

/-- ALL expansion properties are transported to the literal composite
point/sort/colour forgetful functor itself. -/
def historyTransition {A B : CurrentSource.{u,v,w,t}}
    (h : History (fun A B => Nonempty (ActualStep A B)) A B) :
    UnaryTransition A.finiteAge B.finiteAge where
  forget := (historyReduct h).forget
  reasonable := by rw [history_forget_eq]; exact (historyUnary h).reasonable
  reductSurjective := by rw [history_forget_eq]; exact (historyUnary h).reductSurjective
  precompact := by rw [history_forget_eq]; exact (historyUnary h).precompact

/-- The concrete source-step instance gives a terminal homogeneous CCO
source whose actual old reduct projection IS its reasonable precompact
reduct-surjective expansion functor. Zero steps are included. -/
theorem actual_terminalisation_coherent
    (split : ∀ A : CurrentSource.{u,v,w,t}, A.Obstruction →
      ∃ B, Nonempty (ActualStep A B)) (initial : CurrentSource.{u,v,w,t}) :
    ∃ terminal : CurrentSource.{u,v,w,t},
      ∃ history : History (fun A B => Nonempty (ActualStep A B)) initial terminal,
        terminal.Terminal ∧ history.length + terminal.potential ≤ initial.potential ∧
        ∃ reduct : UnaryReduct initial.source terminal.source,
          ∃ unary : UnaryTransition initial.finiteAge terminal.finiteAge,
            unary.forget = reduct.forget := by
  obtain ⟨terminal,h,ht,hbound,_,_⟩ := actual_terminalisation split initial
  exact ⟨terminal,h,ht,hbound,historyReduct h,historyTransition h,rfl⟩

end
end CCO.APCharacter.Towers.CurrentSource
