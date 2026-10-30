import Mathlib.Data.Setoid.Basic
import Mathlib.Order.Quotient
import Mathlib.Data.Fintype.Card

/-! Actual finite nested equivalence diagrams used at the A14 boundary.
No order or function is discarded in an induced embedding. -/
universe u v w
namespace CCO.ResetOrder.Counterexample

structure Nested (X : Type u) where
  P : Setoid X
  Q : Setoid X
  refine : ∀ {x y}, Q.r x y → P.r x y

namespace Nested
variable {X : Type u} {Y : Type v} {Z : Type w}

structure Embedding (A : Nested X) (B : Nested Y) where
  point : X → Y
  injective : Function.Injective point
  p_iff : ∀ x y, B.P.r (point x) (point y) ↔ A.P.r x y
  q_iff : ∀ x y, B.Q.r (point x) (point y) ↔ A.Q.r x y

@[ext] theorem Embedding.ext {A : Nested X} {B : Nested Y}
    {f g : Embedding A B} (h : ∀ x, f.point x = g.point x) : f = g := by
  cases f with
  | mk fp fi fP fQ =>
    cases g with
    | mk gp gi gP gQ =>
      have hp : fp = gp := funext h
      subst gp
      rfl

def Embedding.refl (A : Nested X) : Embedding A A where
  point := id
  injective := Function.injective_id
  p_iff _ _ := Iff.rfl
  q_iff _ _ := Iff.rfl

def Embedding.comp {A : Nested X} {B : Nested Y} {C : Nested Z}
    (g : Embedding B C) (f : Embedding A B) : Embedding A C where
  point := g.point ∘ f.point
  injective := g.injective.comp f.injective
  p_iff x y := (g.p_iff _ _).trans (f.p_iff x y)
  q_iff x y := (g.q_iff _ _).trans (f.q_iff x y)

def induce (A : Nested X) (S : Set X) : Nested S where
  P := A.P.comap Subtype.val
  Q := A.Q.comap Subtype.val
  refine := A.refine

def inclusion (A : Nested X) (S : Set X) : Embedding (A.induce S) A where
  point := Subtype.val
  injective := Subtype.val_injective
  p_iff _ _ := Iff.rfl
  q_iff _ _ := Iff.rfl

/-- Convexity is required for *both* named equivalences. -/
structure ConvexOrder (A : Nested X) where
  order : LinearOrder X
  convexP : ∀ {a b c}, order.le a b → order.le b c → A.P.r a c → A.P.r a b
  convexQ : ∀ {a b c}, order.le a b → order.le b c → A.Q.r a c → A.Q.r a b

namespace ConvexOrder
variable {A : Nested X} {B : Nested Y} {C : Nested Z}

structure Embedding (a : ConvexOrder A) (b : ConvexOrder B) extends A.Embedding B where
  lt_iff : ∀ x y, b.order.lt (point x) (point y) ↔ a.order.lt x y

def Embedding.refl (a : ConvexOrder A) : Embedding a a where
  toEmbedding := Nested.Embedding.refl A
  lt_iff _ _ := Iff.rfl

def Embedding.comp {a : ConvexOrder A} {b : ConvexOrder B} {c : ConvexOrder C}
    (g : Embedding b c) (f : Embedding a b) : Embedding a c where
  toEmbedding := g.toEmbedding.comp f.toEmbedding
  lt_iff x y := (g.lt_iff _ _).trans (f.lt_iff x y)

def induce (a : ConvexOrder A) (S : Set X) : ConvexOrder (A.induce S) where
  order := letI := a.order; inferInstance
  convexP := fun hab hbc hac => a.convexP hab hbc hac
  convexQ := fun hab hbc hac => a.convexQ hab hbc hac

def inclusion (a : ConvexOrder A) (S : Set X) : Embedding (a.induce S) a where
  toEmbedding := A.inclusion S
  lt_iff _ _ := Iff.rfl

end ConvexOrder
end Nested
end CCO.ResetOrder.Counterexample
