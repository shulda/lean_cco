import Mathlib.Data.Set.Image
import Mathlib.Basic.Finite.Defs

/-! Arbitrary signatures, including partial functions of arity zero.
No finiteness or unary restriction is imposed on the signature. -/
universe u v w
namespace CCO.ResetOrder.Generic

structure Language (S : Type u) where
  Func : ℕ → Type u
  Rel : ℕ → Type u
  input : {n : ℕ} → Func n → Fin n → S
  output : {n : ℕ} → Func n → S
  argument : {n : ℕ} → Rel n → Fin n → S

structure Structure {S : Type u} (L : Language S) (V : Type v) where
  sort : V → S
  func : {n : ℕ} → L.Func n → (Fin n → V) → Set V
  functional : ∀ {n} (F : L.Func n) xs y z,
    y ∈ func F xs → z ∈ func F xs → y = z
  func_sorted : ∀ {n} (F : L.Func n) xs y, y ∈ func F xs →
    (∀ i, sort (xs i) = L.input F i) ∧ sort y = L.output F
  rel : {n : ℕ} → L.Rel n → (Fin n → V) → Prop
  rel_sorted : ∀ {n} (R : L.Rel n) xs, rel R xs →
    ∀ i, sort (xs i) = L.argument R i

namespace Structure
variable {S : Type u} {L : Language S} {V : Type v} {W : Type w}

@[ext] theorem ext {C D : Structure L V} (hs : C.sort = D.sort)
    (hf : @C.func = @D.func) (hr : @C.rel = @D.rel) : C = D := by
  cases C
  cases D
  cases hs
  cases hf
  cases hr
  rfl

/-- Closedness retains every defined value, including nullary function values. -/
def Closed (C : Structure L V) (A : Set V) : Prop :=
  ∀ {n} (F : L.Func n) xs, (∀ i, xs i ∈ A) → C.func F xs ⊆ A

/-- Induced embeddings reflect entire function fibres, hence domains as well. -/
structure Embedding (C : Structure L V) (D : Structure L W) where
  point : V → W
  injective : Function.Injective point
  sort_eq : ∀ x, D.sort (point x) = C.sort x
  func_eq : ∀ {n} (F : L.Func n) xs,
    D.func F (point ∘ xs) = point '' C.func F xs
  rel_iff : ∀ {n} (R : L.Rel n) xs,
    D.rel R (point ∘ xs) ↔ C.rel R xs

end Structure
end CCO.ResetOrder.Generic
