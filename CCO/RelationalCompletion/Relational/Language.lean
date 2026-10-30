import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Fintype.EquivFin

/-! Purely relational structures, with arbitrarily many finite-arity symbols.
There are no functions or closure assumptions, and arity zero is allowed. -/
universe u v w z
namespace CCO.RelationalCompletion.Relational

structure Language where
  Rel : ℕ → Type u

structure Structure (L : Language.{u}) (V : Type v) where
  rel : {n : ℕ} → L.Rel n → (Fin n → V) → Prop

namespace Structure
variable {L : Language.{u}} {V : Type v} {W : Type w} {X : Type z}

/-- Every set is an actual induced relational subobject. -/
def induce (A : Structure L V) (S : Set V) : Structure L S where
  rel R xs := A.rel R (Subtype.val ∘ xs)

structure Hom (A : Structure L V) (B : Structure L W) where
  point : V → W
  map_rel : ∀ {n} (R : L.Rel n) xs, A.rel R xs → B.rel R (point ∘ xs)

structure Embedding (A : Structure L V) (B : Structure L W) where
  point : V → W
  injective : Function.Injective point
  rel_iff : ∀ {n} (R : L.Rel n) xs, B.rel R (point ∘ xs) ↔ A.rel R xs

namespace Embedding
variable {A : Structure L V} {B : Structure L W} {C : Structure L X}

def identity (A : Structure L V) : Embedding A A := ⟨id, Function.injective_id, fun _ _ => Iff.rfl⟩

def comp (g : Embedding B C) (f : Embedding A B) : Embedding A C where
  point := g.point ∘ f.point
  injective := g.injective.comp f.injective
  rel_iff R xs := (g.rel_iff R (f.point ∘ xs)).trans (f.rel_iff R xs)

def toHom (f : Embedding A B) : Hom A B := ⟨f.point, fun R xs h => (f.rel_iff R xs).mpr h⟩

end Embedding

def inclusion (A : Structure L V) (S : Set V) : Embedding (A.induce S) A :=
  ⟨Subtype.val, Subtype.val_injective, fun _ _ => Iff.rfl⟩

structure Iso (A : Structure L V) (B : Structure L W) where
  point : V ≃ W
  rel_iff : ∀ {n} (R : L.Rel n) xs, B.rel R (point ∘ xs) ↔ A.rel R xs

namespace Iso
variable {A : Structure L V} {B : Structure L W} {C : Structure L X}

def toEmbedding (f : Iso A B) : Embedding A B := ⟨f.point, f.point.injective, f.rel_iff⟩

def identity (A : Structure L V) : Iso A A := ⟨Equiv.refl V, fun _ _ => Iff.rfl⟩

def trans (f : Iso A B) (g : Iso B C) : Iso A C :=
  ⟨f.point.trans g.point, fun R xs => (g.rel_iff R (f.point ∘ xs)).trans (f.rel_iff R xs)⟩

def symm (f : Iso A B) : Iso B A where
  point := f.point.symm
  rel_iff R xs := by
    have h := f.rel_iff R (f.point.symm ∘ xs)
    have he : (f.point : V → W) ∘ ((f.point.symm : W → V) ∘ xs) = xs :=
      funext (fun i => f.point.apply_symm_apply (xs i))
    rw [he] at h
    exact h.symm

end Iso

/-- A pair of induced factors freely covers A exactly when every positive tuple
lies wholly in one factor. Their intersection is unrestricted and may be empty. -/
def FreeSplit (A : Structure L V) (P Q : Set V) : Prop :=
  P ∪ Q = Set.univ ∧ ∀ {n} (R : L.Rel n) xs, A.rel R xs →
    (∀ i, xs i ∈ P) ∨ (∀ i, xs i ∈ Q)

def Irreducible (A : Structure L V) : Prop :=
  ∀ P Q, A.FreeSplit P Q → P = Set.univ ∨ Q = Set.univ

/-- The SAME map, injective and induced on the indicated source subset. -/
def EmbedsOn (A : Structure L V) (B : Structure L W) (h : V → W) (S : Set V) : Prop :=
  Set.InjOn h S ∧ ∀ {n} (R : L.Rel n) xs, (∀ i, xs i ∈ S) →
    (B.rel R (h ∘ xs) ↔ A.rel R xs)

structure IsHE (A : Structure L V) (B : Structure L W) (h : V → W) : Prop where
  positive : ∀ {n} (R : L.Rel n) xs, A.rel R xs → B.rel R (h ∘ xs)
  irreducible : ∀ S, (A.induce S).Irreducible → A.EmbedsOn B h S

/-- The target-induced pullbacks agree on each protected set separately.
With injectivity of both restrictions this induces an ACTUAL isomorphism
between their target images; it does not assert any source reflection. -/
def SameImageType (B : Structure L W) (h k : V → W) (S : Set V) : Prop :=
  ∀ {n} (R : L.Rel n) xs, (∀ i, xs i ∈ S) →
    (B.rel R (h ∘ xs) ↔ B.rel R (k ∘ xs))

namespace SameImageType
variable {B : Structure L W} {h k l : V → W} {S : Set V}

theorem refl : B.SameImageType h h S := fun _ _ _ => Iff.rfl

theorem trans (a : B.SameImageType h k S) (b : B.SameImageType k l S) :
    B.SameImageType h l S := fun R xs hx => (a R xs hx).trans (b R xs hx)

end SameImageType
end Structure
end CCO.RelationalCompletion.Relational
