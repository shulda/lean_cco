import CCO.FullCode.Roots

/-! Literal finite hidden models and heredity under closed induced
substructures. These definitions assume neither Ramsey nor EP. -/
universe u v
namespace CCO.FullCode

structure FiniteHidden (L : Language.{u}) where
  Carrier : Type v
  model : Structure L Carrier
  finite : Finite Carrier

attribute [instance] FiniteHidden.finite

namespace FiniteHidden
variable {L : Language.{u}}

def induced (D : FiniteHidden.{u,v} L) (T : Set D.Carrier) (closed : D.model.IsClosed T) :
    FiniteHidden.{u,v} L where
  Carrier := T
  model := D.model.induce T closed
  finite := inferInstance

def support {S : RootScheme L} {A : Type*} (D : FiniteHidden.{u,v} L)
    (O : Object D.model S A) : FiniteHidden.{u,v} L :=
  D.induced O.support (D.model.isClosed_closure O.coordinates)

end FiniteHidden

def HereditaryHidden {L : Language.{u}} (H : FiniteHidden.{u,v} L → Prop) : Prop :=
  ∀ D, H D → ∀ (T : Set D.Carrier) (closed : D.model.IsClosed T), H (D.induced T closed)

/-- Generated supports belong to the SAME age, including the empty one. -/
theorem support_in_hidden_age {L : Language.{u}} {S : RootScheme L} {A : Type*}
    {H : FiniteHidden.{u,v} L → Prop} (hereditary : HereditaryHidden H)
    (D : FiniteHidden.{u,v} L) (member : H D) (O : Object D.model S A) :
    H (D.support O) :=
  hereditary D member O.support (D.model.isClosed_closure O.coordinates)

end CCO.FullCode
