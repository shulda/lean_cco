import CCO.FullPhaseLift.Full.Partial

/-! Complete induced OLD factors include every negative tuple and nullary.
Their individual age witnesses are actual embeddings of those factors,
not a completion or amalgamation premise for the whole partial diagram. -/

universe v w
namespace CCO.FullPhaseLift.Full
open Canonical
variable {L : Signature} {M : Type w} {V : Type v}

structure FrozenFactor (U : BoolTable L M) (D : Partial L V) where
  size : ℕ
  inclusion : Fin size ↪ V
  table : BoolTable L (Fin size)
  age : Nonempty (Embedding table U)
  agrees : ∀ r xs, D r (inclusion ∘ xs) = some (table r xs)

namespace FrozenFactor
def FixedBy {U : BoolTable L M} {D : Partial L V} (F : FrozenFactor U D)
    (f : V → M) : Prop :=
  Function.Injective (f ∘ F.inclusion) ∧
    ∀ r xs, U r (f ∘ F.inclusion ∘ xs) = F.table r xs

theorem fixedBy_of_realizes {U : BoolTable L M} {D : Partial L V}
    (F : FrozenFactor U D) (f : V → M) (h : Realizes U D f)
    (hi : Function.Injective (f ∘ F.inclusion)) : F.FixedBy f :=
  ⟨hi,fun r xs => h r (F.inclusion ∘ xs) (F.table r xs) (F.agrees r xs)⟩

def fixedEmbedding {U : BoolTable L M} {D : Partial L V} (F : FrozenFactor U D)
    (f : V → M) (h : F.FixedBy f) : Embedding F.table U :=
  embeddingOf (f ∘ F.inclusion) h.1 h.2

def augment {U : BoolTable L M} {D : Partial L V} (F : FrozenFactor U D)
    (p : V → M) (hp : LowRealizes U D p) : FrozenFactor U (augmentLow U D p) where
  size := F.size
  inclusion := F.inclusion
  table := F.table
  age := F.age
  agrees r xs := augmentLow_extends U D p hp r _ _ (F.agrees r xs)
end FrozenFactor

def HigherCovered {U : BoolTable L M} {D : Partial L V} {m : ℕ}
    (F : Fin m → FrozenFactor U D) : Prop :=
  ∀ r xs b, D r xs = some b → ¬ SmallSupport xs →
    ∃ j, Set.range xs ⊆ Set.range (F j).inclusion

theorem higherCovered_augment {U : BoolTable L M} {D : Partial L V} {m : ℕ}
    (F : Fin m → FrozenFactor U D) (hF : HigherCovered F)
    (p : V → M) (hp : LowRealizes U D p) :
    HigherCovered (fun j => (F j).augment p hp) := by
  intro r xs b hd hs
  rw [augmentLow_high U D p r xs hs] at hd
  exact hF r xs b hd hs

/-- A WEAK low realization. This alone is NOT the cycle-constrained source
pair-completion premise: collisions can hide signed low constraints. -/
def WeakPairCompletion (U : BoolTable L M) (D : Partial L V) {m : ℕ}
    (F : Fin m → FrozenFactor U D) : Prop :=
  ∃ p : V → M, LowRealizes U D p ∧
    ∀ j, Function.Injective (p ∘ (F j).inclusion)

/-- INTERNAL strict semantic pair target. The actual source interface uses
an atomic canonical shadow refinement and CycleHom certificates; the proved
source-shadow bridge converts between that premise and this target.
This is never presented as an unexplained negative-menu injectivization. -/
def PairCompletion (U : BoolTable L M) (D : Partial L V) {m : ℕ}
    (F : Fin m → FrozenFactor U D) : Prop :=
  ∃ p : V ↪ M, LowRealizes U D p ∧
    ∀ j, Function.Injective ((p : V → M) ∘ (F j).inclusion)

theorem PairCompletion.of_actual {U : BoolTable L M} {D : Partial L V} {m : ℕ}
    (F : Fin m → FrozenFactor U D) (p : V ↪ M) (hp : LowRealizes U D p) :
    PairCompletion U D F :=
  ⟨p,hp,fun j => p.injective.comp (F j).inclusion.injective⟩

/-- INTERNAL strict-semantic completion interface, on finite ordinal charts.
The source gate remains the fully quantified certified-shadow A03, with a
proved equivalence at each actual homogeneous SAP+CCO canonical prefix. -/
def StrictSupportNormal (U : BoolTable L M) : Prop :=
  ∀ (n : ℕ) (D : Partial L (Fin n)) (m : ℕ) (F : Fin m → FrozenFactor U D),
    Consistent U D → HigherCovered F → PairCompletion U D F →
    ∃ f : Fin n → M, Realizes U D f ∧ ∀ j, (F j).FixedBy f

/-- Temporary compatible INTERNAL spelling for the strict-semantic lemma
library. Source exports must use the certified-shadow interface/bridge. -/
abbrev SupportNormal (U : BoolTable L M) : Prop := StrictSupportNormal U

end CCO.FullPhaseLift.Full
