import CCO.APCharacter.Towers.FiniteHistory
import CCO.APCharacter.Towers.UnaryComposition

/-! Finite histories of actual unary expansion functors compose to one
actual original-to-terminal reduct functor, retaining all three expansion
properties without postulating a separate composite provider. -/
universe u v
namespace CCO.APCharacter.Towers
noncomputable section

/-- A transition exists only with concrete functor and property data. -/
def UnaryStep (A B : UnaryAge.{u,v}) : Prop := Nonempty (UnaryTransition A B)

namespace History

def unaryComposite {A B : UnaryAge.{u,v}} (h : History UnaryStep A B) : UnaryTransition A B := by
  induction h with
  | nil A => exact UnaryTransition.identity A
  | cons hs tail ih => exact (Classical.choice hs).compose ih

theorem unaryProperties {A B : UnaryAge.{u,v}} (h : History UnaryStep A B) :
    Reasonable h.unaryComposite.forget ∧
      ReductSurjective h.unaryComposite.forget ∧ Precompact h.unaryComposite.forget :=
  ⟨h.unaryComposite.reasonable,h.unaryComposite.reductSurjective,h.unaryComposite.precompact⟩

end History

/-- Concrete unary expansion data can be extracted from any actual source
step, and composed along its finite source history. This does not assume
that different stages have identical diagram categories. -/
def finiteUnaryComposite {Source : Type*} {Step : Source → Source → Prop}
    (age : Source → UnaryAge.{u,v})
    (forgetStep : ∀ {A B}, Step A B → UnaryTransition (age A) (age B))
    {A B : Source} (h : History Step A B) : UnaryTransition (age A) (age B) := by
  induction h with
  | nil A => exact UnaryTransition.identity (age A)
  | cons hs tail ih => exact (forgetStep hs).compose ih

end
end CCO.APCharacter.Towers
