import CCO.UnaryHN.Ordered.Completion

/-! Explicit source cycle claims. The GIVEN ambient map need not be
injective. Transport to the old completion uses the DIFFERENT genuine E02
injection. These lemmas retain that distinction. -/

universe u v
namespace CCO.UnaryHN.Native

open StructuralRamsey
open StructuralRamsey.Structure

def displayedOrder {L : Language.{u}} {V : Type v}
    (C : Structure L.withLinearOrder V) (x y : V) : Prop := C.rel (.inr ()) ![x, y]

theorem no_cycles_of_strict_map {V P : Type v} [Preorder P]
    {R : V → V → Prop} (p : V → P) (hp : ∀ x y, R x y → p x < p y) :
    ∀ x, ¬ Relation.TransGen R x x := by
  have hPath : ∀ {x y}, Relation.TransGen R x y → p x < p y := by
    intro x y h
    induction h with
    | single h => exact hp _ _ h
    | tail h edge ih => exact lt_trans ih (hp _ _ edge)
  intro x h
  exact lt_irrefl (p x) (hPath h)

theorem displayed_order_no_cycles {L : Language.{u}} {V P : Type v}
    (C : Structure L.withLinearOrder V) (D : Structure L.withLinearOrder P)
    (hD : AllOrderedModels L D) (p : V → P) (hp : HE C D p) :
    ∀ x, ¬ Relation.TransGen (displayedOrder C) x x := by
  rcases hD with ⟨old, o, _, rfl⟩
  let : LinearOrder P := o
  exact no_cycles_of_strict_map p (fun x y h => hp.1.1 (.inr ()) ![x, y] h)

def transportedRelation {V W : Type v} (g : V → W) (R : V → V → Prop) (a b : W) : Prop :=
  ∃ x y, g x = a ∧ g y = b ∧ R x y

theorem transGen_transport_lift {V W : Type v} {g : V → W} (hg : Function.Injective g)
    {R : V → V → Prop} {a b : W} (h : Relation.TransGen (transportedRelation g R) a b) :
    ∃ x y, g x = a ∧ g y = b ∧ Relation.TransGen R x y := by
  induction h with
  | single h =>
      obtain ⟨x, y, hx, hy, hxy⟩ := h
      exact ⟨x, y, hx, hy, .single hxy⟩
  | tail h edge ih =>
      obtain ⟨x, y, hx, hy, hxy⟩ := ih
      obtain ⟨z, t, hz, ht, hzt⟩ := edge
      have hzy : z = y := hg (hz.trans hy.symm)
      subst z
      exact ⟨x, t, hx, ht, hxy.tail hzt⟩

theorem no_cycles_transport {V W : Type v} {g : V → W} (hg : Function.Injective g)
    {R : V → V → Prop} (hR : ∀ x, ¬ Relation.TransGen R x x) :
    ∀ a, ¬ Relation.TransGen (transportedRelation g R) a a := by
  intro a h
  obtain ⟨x, y, hx, hy, hxy⟩ := transGen_transport_lift hg h
  have heq : x = y := hg (hx.trans hy.symm)
  subst y
  exact hR x hxy

theorem transported_order_no_cycles {L : Language.{u}} {V W P : Type v}
    (C : Structure L.withLinearOrder V) (Old : Structure L W)
    (D : Structure L.withLinearOrder P) (hD : AllOrderedModels L D)
    (p : V → P) (hp : HE C D p) (g : V → W) (hg : Function.Injective g) :
    ∀ a, ¬ Relation.TransGen (displayedOrder (transportedOrder C Old g)) a a :=
  no_cycles_transport hg (displayed_order_no_cycles C D hD p hp)

end CCO.UnaryHN.Native
