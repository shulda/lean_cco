import CCO.RelationalCompletion.Relational.Homogeneous
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Fintype.Pi

/-! The one normalized finite full relational signature used by B048.
Every old relation and every tuple is retained, including arity zero and
repeated coordinates. Bool tables distinguish complete data from partial
Option Bool declarations in the completion interface. -/

universe v w z
namespace CCO.FullPhaseLift.Canonical
namespace R
abbrev Language := RelationalCompletion.Relational.Language
abbrev Structure := RelationalCompletion.Relational.Structure
end R

structure Signature where
  size : ℕ
  arity : Fin size → ℕ

def Signature.language (L : Signature) : R.Language where
  Rel n := {r : Fin L.size // L.arity r = n}

abbrev BoolTable (L : Signature) (V : Type v) :=
  (r : Fin L.size) → (Fin (L.arity r) → V) → Bool

def pullback {L : Signature} {V : Type v} {W : Type w}
    (T : BoolTable L V) (f : W → V) : BoolTable L W :=
  fun r xs => T r (f ∘ xs)

def toRelational {L : Signature} {V : Type v} (T : BoolTable L V) :
    R.Structure L.language V where
  rel R xs := T R.val (xs ∘ Fin.cast R.property) = true

@[simp] theorem toRelational_read {L : Signature} {V : Type v}
    (T : BoolTable L V) (r : Fin L.size) (xs : Fin (L.arity r) → V) :
    (toRelational T).rel (⟨r,rfl⟩ : L.language.Rel (L.arity r)) xs ↔ T r xs = true := Iff.rfl

noncomputable def ofRelational {L : Signature} {V : Type v}
    (A : R.Structure L.language V) : BoolTable L V :=
  fun r xs => by
    classical
    exact decide (A.rel ⟨r,rfl⟩ xs)

@[simp] theorem ofRelational_toRelational {L : Signature} {V : Type v}
    (T : BoolTable L V) : ofRelational (toRelational T) = T := by
  funext r xs
  simp only [ofRelational, toRelational, Fin.cast_refl, Function.comp_id]
  exact Bool.decide_coe (T r xs)

@[simp] theorem toRelational_ofRelational {L : Signature} {V : Type v}
    (A : R.Structure L.language V) : toRelational (ofRelational A) = A := by
  classical
  have h : @RelationalCompletion.Relational.Structure.rel _ _
      (toRelational (ofRelational A)) = @RelationalCompletion.Relational.Structure.rel _ _ A := by
    funext n R xs
    rcases R with ⟨r,hn⟩
    subst n
    simp [toRelational,ofRelational]
  exact congrArg RelationalCompletion.Relational.Structure.mk h

abbrev Embedding {L : Signature} {V : Type v} {W : Type w}
    (A : BoolTable L V) (B : BoolTable L W) :=
  RelationalCompletion.Relational.Structure.Embedding (toRelational A) (toRelational B)

abbrev Iso {L : Signature} {V : Type v} {W : Type w}
    (A : BoolTable L V) (B : BoolTable L W) :=
  RelationalCompletion.Relational.Structure.Iso (toRelational A) (toRelational B)

theorem embedding_read {L : Signature} {V : Type v} {W : Type w}
    {A : BoolTable L V} {B : BoolTable L W} (e : Embedding A B)
    (r : Fin L.size) (xs : Fin (L.arity r) → V) :
    B r (e.point ∘ xs) = A r xs := by
  have h := e.rel_iff (⟨r,rfl⟩ : L.language.Rel (L.arity r)) xs
  change (B r (e.point ∘ xs) = true ↔ A r xs = true) at h
  cases hb : B r (e.point ∘ xs) <;> cases ha : A r xs <;> simp_all

def embeddingOf {L : Signature} {V : Type v} {W : Type w}
    {A : BoolTable L V} {B : BoolTable L W} (f : V → W)
    (hf : Function.Injective f)
    (h : ∀ r xs, B r (f ∘ xs) = A r xs) : Embedding A B where
  point := f
  injective := hf
  rel_iff R xs := by
    rcases R with ⟨r,hr⟩
    subst hr
    change (B r (f ∘ xs) = true ↔ A r xs = true)
    rw [h]

theorem iso_read {L : Signature} {V : Type v} {W : Type w}
    {A : BoolTable L V} {B : BoolTable L W} (e : Iso A B)
    (r : Fin L.size) (xs : Fin (L.arity r) → V) :
    B r (e.point ∘ xs) = A r xs := embedding_read e.toEmbedding r xs

def isoOf {L : Signature} {V : Type v} {W : Type w}
    {A : BoolTable L V} {B : BoolTable L W} (f : V ≃ W)
    (h : ∀ r xs, B r (f ∘ xs) = A r xs) : Iso A B :=
  { (embeddingOf (f : V → W) f.injective h) with point := f }

/-- Exact finite symbol set, even though the arities may be arbitrarily large. -/
def symbolEquiv (L : Signature) : (Σ n, L.language.Rel n) ≃ Fin L.size where
  toFun s := s.2.val
  invFun r := ⟨L.arity r,⟨r,rfl⟩⟩
  left_inv s := by rcases s with ⟨n,r,h⟩; subst n; rfl
  right_inv _ := rfl

instance (L : Signature) : Finite (Σ n, L.language.Rel n) :=
  Finite.of_equiv (Fin L.size) (symbolEquiv L).symm

/-- Every relation instance using at most k variable slots, with ALL maps
from the original arity. Arity-zero symbols contribute their unique map. -/
abbrev AtomicTest (L : Signature) (k : ℕ) :=
  Σ r : Fin L.size, (Fin (L.arity r) → Fin k)

instance (L : Signature) (k : ℕ) : Fintype (AtomicTest L k) := inferInstance

abbrev Profile (L : Signature) (k : ℕ) := AtomicTest L k → Bool

def profile {L : Signature} {V : Type v} (T : BoolTable L V) {k : ℕ}
    (p : Fin k → V) : Profile L k := fun a => T a.1 (p ∘ a.2)

@[simp] theorem profile_embedding {L : Signature} {V : Type v} {W : Type w}
    {A : BoolTable L V} {B : BoolTable L W} (e : Embedding A B)
    {k : ℕ} (p : Fin k → V) : profile B (e.point ∘ p) = profile A p := by
  funext a
  exact embedding_read e a.1 (p ∘ a.2)

end CCO.FullPhaseLift.Canonical
