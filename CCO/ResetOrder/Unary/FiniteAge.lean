import CCO.ResetOrder.Unary.Category
import Mathlib.Basic.Finite.Set

universe u v
namespace CCO.ResetOrder.Unary
open CCO.UnarySupport

structure Object (L : Signature.{u}) where
  Carrier : Type v
  finite : Finite Carrier
  data : Structure L Carrier
attribute [instance] Object.finite

abbrev Object.Emb {L : Signature.{u}} (A B : Object.{u,v} L) := Hom A.data B.data
abbrev Age (L : Signature.{u}) := Object.{u,v} L → Prop

def Hereditary {L : Signature.{u}} (K : Age.{u,v} L) : Prop :=
  ∀ {A B}, K A → Nonempty (B.Emb A) → K B

def Object.induce {L : Signature.{u}} (A : Object.{u,v} L)
    (S : Set A.Carrier) (hS : A.data.IsClosed S) : Object.{u,v} L where
  Carrier := S
  finite := inferInstance
  data := A.data.induce S hS

def Object.inclusion {L : Signature.{u}} (A : Object.{u,v} L)
    (S : Set A.Carrier) (hS : A.data.IsClosed S) : (A.induce S hS).Emb A :=
  A.data.inclusion S hS

def Arrow {L : Signature.{u}} (A B C : Object.{u,v} L) (k : ℕ) : Prop :=
  ∀ color : A.Emb C → Fin k, ∃ g : B.Emb C, ∃ shade : Fin k,
    ∀ f : A.Emb B, color (compose g f) = shade

def Ramsey {L : Signature.{u}} (K : Age.{u,v} L) : Prop :=
  ∀ A B, K A → K B → ∀ k, 0 < k → ∃ C, K C ∧ Arrow A B C k

def JEP {L : Signature.{u}} (K : Age.{u,v} L) : Prop :=
  ∀ A B, K A → K B → ∃ C, K C ∧ Nonempty (A.Emb C) ∧ Nonempty (B.Emb C)

def SAP {L : Signature.{u}} (K : Age.{u,v} L) : Prop :=
  ∀ P A B, K P → K A → K B → ∀ (i : P.Emb A) (j : P.Emb B),
    ∃ C, K C ∧ ∃ (f : A.Emb C) (g : B.Emb C),
      (∀ p, f.point (i.point p) = g.point (j.point p)) ∧
      ∀ a b, f.point a = g.point b → ∃ p, i.point p = a ∧ j.point p = b

end CCO.ResetOrder.Unary
