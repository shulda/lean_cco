import Mathlib.Data.Set.Image

/-! Arbitrary typed signatures with genuine single-valued PARTIAL unary maps.
B036-local generalization of the accepted B034 primitives: only symbol/sort
finiteness fields are removed; no accepted file or API is changed.
Relation arities may be zero; no constant or higher-arity function is present. -/
universe u v w
namespace CCO.ResetOrder.Unary.Primitive

structure Signature where
  Sorts : Type u
  Func : Type u
  Rel : Type u
  input : Func → Sorts
  output : Func → Sorts
  arity : Rel → ℕ
  argument : (R : Rel) → Fin (arity R) → Sorts


structure Structure (L : Signature.{u}) (V : Type v) where
  sort : V → L.Sorts
  func : L.Func → V → Set V
  functional : ∀ F x y z, y ∈ func F x → z ∈ func F x → y = z
  func_sorted : ∀ F x y, y ∈ func F x → sort x = L.input F ∧ sort y = L.output F
  rel : (R : L.Rel) → (Fin (L.arity R) → V) → Prop
  rel_sorted : ∀ R xs, rel R xs → ∀ i, sort (xs i) = L.argument R i

namespace Structure
variable {L : Signature.{u}} {V : Type v} {W : Type w}

def Total (C : Structure L V) : Prop :=
  ∀ F x, C.sort x = L.input F → (C.func F x).Nonempty

def IsClosed (C : Structure L V) (S : Set V) : Prop :=
  ∀ F x, x ∈ S → C.func F x ⊆ S

structure Hom (C : Structure L V) (D : Structure L W) where
  point : V → W
  sort_eq : ∀ x, D.sort (point x) = C.sort x
  map_func : ∀ F x y, y ∈ C.func F x → point y ∈ D.func F (point x)
  map_rel : ∀ R xs, C.rel R xs → D.rel R (point ∘ xs)

structure Embedding (C : Structure L V) (D : Structure L W) extends Hom C D where
  injective : Function.Injective point
  reflect_func : ∀ F x y, y ∈ D.func F (point x) → ∃ z, z ∈ C.func F x ∧ point z = y
  reflect_rel : ∀ R xs, D.rel R (point ∘ xs) → C.rel R xs

theorem Embedding.map_func_eq {C : Structure L V} {D : Structure L W}
    (f : Embedding C D) (F : L.Func) (x : V) :
    D.func F (f.point x) = f.point '' C.func F x := by
  ext y
  constructor
  · exact f.reflect_func F x y
  · rintro ⟨z, hz, rfl⟩
    exact f.map_func F x z hz

theorem Embedding.domain_iff {C : Structure L V} {D : Structure L W}
    (f : Embedding C D) (F : L.Func) (x : V) :
    (D.func F (f.point x)).Nonempty ↔ (C.func F x).Nonempty := by
  constructor
  · rintro ⟨y, hy⟩
    obtain ⟨z, hz, _⟩ := f.reflect_func F x y hy
    exact ⟨z, hz⟩
  · rintro ⟨z, hz⟩
    exact ⟨f.point z, f.map_func F x z hz⟩

end Structure
end CCO.ResetOrder.Unary.Primitive
