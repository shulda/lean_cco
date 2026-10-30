import CCO.FullPhaseLift.Canonical.Signature
import Mathlib.Data.Fintype.Card

/-! Genuine signed partial FULL relational diagrams. `none` is unspecified;
`some false` is a negative declaration. Arbitrary old arities, repeated
coordinates and nullaries are retained without an arity truncation. -/

universe v w z
namespace CCO.FullPhaseLift.Full
open Canonical

abbrev Partial (L : Signature) (V : Type v) :=
  (r : Fin L.size) → (Fin (L.arity r) → V) → Option Bool

/-- Precisely support at most two, including the empty tuple. -/
def SmallSupport {n : ℕ} {V : Type v} (xs : Fin n → V) : Prop :=
  ∀ i j k, xs i = xs j ∨ xs i = xs k ∨ xs j = xs k

theorem SmallSupport.comp {n : ℕ} {V : Type v} {W : Type w}
    {xs : Fin n → V} (h : SmallSupport xs) (f : V → W) : SmallSupport (f ∘ xs) := by
  intro i j k
  rcases h i j k with he | he | he
  · exact Or.inl (congrArg f he)
  · exact Or.inr (Or.inl (congrArg f he))
  · exact Or.inr (Or.inr (congrArg f he))

theorem smallSupport_fin {n k : ℕ} (hk : k ≤ 2) (xs : Fin n → Fin k) :
    SmallSupport xs := by
  have h2 : ∀ a b c : Fin 2, a = b ∨ a = c ∨ b = c := by decide
  intro i j l
  let f : Fin k → Fin 2 := Fin.castLE hk
  have hinj : Function.Injective f :=
    fun a b h => Fin.ext (congrArg (fun z : Fin 2 => z.val) h)
  rcases h2 (f (xs i)) (f (xs j)) (f (xs l)) with he | he | he
  · exact Or.inl (hinj he)
  · exact Or.inr (Or.inl (hinj he))
  · exact Or.inr (Or.inr (hinj he))

def Realizes {L : Signature} {M : Type w} {V : Type v}
    (U : BoolTable L M) (D : Partial L V) (f : V → M) : Prop :=
  ∀ r xs b, D r xs = some b → U r (f ∘ xs) = b

def LowRealizes {L : Signature} {M : Type w} {V : Type v}
    (U : BoolTable L M) (D : Partial L V) (f : V → M) : Prop :=
  ∀ r xs b, SmallSupport xs → D r xs = some b → U r (f ∘ xs) = b

theorem Realizes.low {L : Signature} {M : Type w} {V : Type v}
    {U : BoolTable L M} {D : Partial L V} {f : V → M}
    (h : Realizes U D f) : LowRealizes U D f := fun r xs b _ => h r xs b

namespace Partial
def pullback {L : Signature} {V : Type v} {W : Type w}
    (D : Partial L V) (f : W → V) : Partial L W := fun r xs => D r (f ∘ xs)
end Partial

/-- Canonical consistency is LOCAL actual unary/two-point consistency.
It does not assume a full old realization of the whole partial diagram.
Single-valued Option Bool already forbids contrary signed declarations. -/
def Consistent {L : Signature} {M : Type w} {V : Type v}
    (U : BoolTable L M) (D : Partial L V) : Prop :=
  ∀ n : ℕ, n ≤ 2 → ∀ j : Fin n ↪ V,
    ∃ p : Fin n ↪ M, Realizes U (D.pullback j) p

/-- Fill only support-at-most-two information from a CHOSEN actual pair
target. In particular no higher-support positive OR negative tuple changes. -/
noncomputable def augmentLow {L : Signature} {M : Type w} {V : Type v}
    (U : BoolTable L M) (D : Partial L V) (p : V → M) : Partial L V := by
  classical
  exact fun r xs => if SmallSupport xs then some (U r (p ∘ xs)) else D r xs

theorem augmentLow_small {L : Signature} {M : Type w} {V : Type v}
    (U : BoolTable L M) (D : Partial L V) (p : V → M) r xs (h : SmallSupport xs) :
    augmentLow U D p r xs = some (U r (p ∘ xs)) := by
  classical
  exact if_pos h

theorem augmentLow_high {L : Signature} {M : Type w} {V : Type v}
    (U : BoolTable L M) (D : Partial L V) (p : V → M) r xs (h : ¬ SmallSupport xs) :
    augmentLow U D p r xs = D r xs := by
  classical
  exact if_neg h

theorem augmentLow_extends {L : Signature} {M : Type w} {V : Type v}
    (U : BoolTable L M) (D : Partial L V) (p : V → M) (hp : LowRealizes U D p)
    r xs b (hd : D r xs = some b) : augmentLow U D p r xs = some b := by
  classical
  by_cases hs : SmallSupport xs
  · rw [augmentLow_small U D p r xs hs,hp r xs b hs hd]
  · exact (augmentLow_high U D p r xs hs).trans hd

theorem augmentLow_consistent {L : Signature} {M : Type w} {V : Type v}
    (U : BoolTable L M) (D : Partial L V) (p : V ↪ M) :
    Consistent U (augmentLow U D p) := by
  intro n hn j
  refine ⟨j.trans p,?_⟩
  intro r xs b hd
  have hs : SmallSupport (j ∘ xs) := (smallSupport_fin hn xs).comp j
  change augmentLow U D p r (j ∘ xs) = some b at hd
  rw [augmentLow_small U D p r (j ∘ xs) hs] at hd
  exact Option.some.inj hd

end CCO.FullPhaseLift.Full
