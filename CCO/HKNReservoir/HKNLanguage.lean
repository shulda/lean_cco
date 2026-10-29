import AllThoseEPPA.Substructure
import Mathlib.Data.Fin.VecNotation

/-! Literal CCO-to-HKN language. There is no equality/none relation.
Named total translations are singleton-valued unary set-functions. -/
universe u v w z x
namespace CCO.HKNReservoir
open AllThoseEPPA

inductive Rel (B : Type u) (K : Type v) (Atom : Type w) : ℕ → Type (max u v w)
  | owner : B → Rel B K Atom 1
  | fine : Atom → Rel B K Atom 2

inductive Func (B : Type u) (K : Type v) (Atom : Type w) : ℕ → Type (max u v w)
  | translate : K → Func B K Atom 1

def Signature (B : Type u) (K : Type v) (Atom : Type w) : Language.{max u v w} where
  RelSymbol := Rel B K Atom
  FuncSymbol := Func B K Atom
  relArity_pos := by intro n R; cases R <;> decide

instance (B : Type u) (K : Type v) (Atom : Type w) : (Signature B K Atom).HasUnaryFunctions where
  arity_eq_one := by intro n F; cases F; rfl

namespace Rel
variable {B : Type u} {K : Type v} {Atom : Type w}

def ownerMove (e : Equiv.Perm B) {n : ℕ} : Rel B K Atom n ≃ Rel B K Atom n where
  toFun | .owner b => .owner (e b) | .fine a => .fine a
  invFun | .owner b => .owner (e.symm b) | .fine a => .fine a
  left_inv := by intro R; cases R <;> simp
  right_inv := by intro R; cases R <;> simp

@[simp] theorem ownerMove_owner (e : Equiv.Perm B) (b : B) : ownerMove (K:=K) (Atom:=Atom) e (.owner b) = .owner (e b) := rfl
@[simp] theorem ownerMove_fine (e : Equiv.Perm B) (a : Atom) : ownerMove (K:=K) e (.fine a) = .fine a := rfl
end Rel

/-- Exactly one global owner permutation acts on every relation symbol. -/
def action {B : Type u} {K : Type v} {Atom : Type w} {Γ : Type z} [Group Γ]
    (tag : Γ →* Equiv.Perm B) : (Signature B K Atom).Action Γ where
  rel n := {
    toFun := fun g => Rel.ownerMove (tag g)
    map_one' := by
      apply Equiv.ext
      intro R
      change Rel.ownerMove (tag 1) R = R
      cases R <;> simp [Rel.ownerMove]
    map_mul' := by
      intro g h
      apply Equiv.ext
      intro R
      change Rel.ownerMove (tag (g*h)) R = Rel.ownerMove (tag g) (Rel.ownerMove (tag h) R)
      cases R <;> simp [Rel.ownerMove,Equiv.Perm.mul_apply] }
  func _ := 1

@[simp] theorem action_owner {B : Type u} {K : Type v} {Atom : Type w} {Γ : Type z} [Group Γ]
    (tag : Γ →* Equiv.Perm B) (g : Γ) (b : B) :
    (action (K:=K) (Atom:=Atom) tag).onRel g (.owner b) = .owner (tag g b) := rfl
@[simp] theorem action_fine {B : Type u} {K : Type v} {Atom : Type w} {Γ : Type z} [Group Γ]
    (tag : Γ →* Equiv.Perm B) (g : Γ) (a : Atom) :
    (action (K:=K) tag).onRel g (.fine a) = .fine a := rfl
@[simp] theorem action_translate {B : Type u} {K : Type v} {Atom : Type w} {Γ : Type z} [Group Γ]
    (tag : Γ →* Equiv.Perm B) (g : Γ) (k : K) :
    (action (Atom:=Atom) tag).onFunc g (.translate k) = .translate k := rfl

/-- Concrete source data; no such functionality or packet axioms are
assumed for an arbitrary external HKN output structure. -/
structure Data (B : Type u) (K : Type v) (Atom : Type w) (V : Type x) where
  owner : V → B
  fine : Atom → V → V → Prop
  move : K → V → V

def encode {B : Type u} {K : Type v} {Atom : Type w} {V : Type x}
    (D : Data B K Atom V) : Structure (Signature B K Atom) V where
  rel
    | .owner b, xs => D.owner (xs 0) = b
    | .fine a, xs => D.fine a (xs 0) (xs 1)
  func | .translate k, xs => {D.move k (xs 0)}

@[simp] theorem encode_owner {B : Type u} {K : Type v} {Atom : Type w} {V : Type x}
    (D : Data B K Atom V) (b : B) (xs : Fin 1 → V) : (encode D).rel (.owner b) xs ↔ D.owner (xs 0) = b := Iff.rfl
@[simp] theorem encode_fine {B : Type u} {K : Type v} {Atom : Type w} {V : Type x}
    (D : Data B K Atom V) (a : Atom) (xs : Fin 2 → V) : (encode D).rel (.fine a) xs ↔ D.fine a (xs 0) (xs 1) := Iff.rfl
@[simp] theorem encode_translate {B : Type u} {K : Type v} {Atom : Type w} {V : Type x}
    (D : Data B K Atom V) (k : K) (xs : Fin 1 → V) : (encode D).func (.translate k) xs = {D.move k (xs 0)} := rfl

/-- Functional closure means closure under EVERY displayed translation. -/
theorem isClosed_encode_iff {B : Type u} {K : Type v} {Atom : Type w} {V : Type x}
    (D : Data B K Atom V) (A : Set V) :
    (encode D).IsClosed A ↔ ∀ k x, x ∈ A → D.move k x ∈ A := by
  constructor
  · intro hc k x hx
    exact hc (.translate k) (fun _ => x) (fun _ => hx) (Set.mem_singleton _)
  · intro hc n F xs hxs y hy
    cases F with
    | translate k =>
      have he : y = D.move k (xs 0) := hy
      exact he ▸ hc k (xs 0) (hxs 0)

end CCO.HKNReservoir
