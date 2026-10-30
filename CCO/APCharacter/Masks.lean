import CCO.RigidGroupoid.Geometry.Basic
import Mathlib.Data.ZMod.Basic

/-! Local phase masks and their equality-inclusive exact calculus. These are
interfaces for the independent finite completion argument; the actual maximal
source gates construct every field in the receiving source instance. -/
universe u v w z
namespace CCO.APCharacter
open RigidGroupoid.Geometry
abbrev Bit := ZMod 2
variable {ι : Type u} {X : ι → Type v} (S : AtomicSource.{u,v,w} ι X)

structure MaskData where
  validBit : ι → Bit → Prop
  allowed : ∀ {i j : ι}, Option (S.Atom i j) → Bit → Bit → Prop
  reverse : ∀ {i j} (a : S.Atom i j) (ε η : Bit),
    allowed (some a) ε η ↔ allowed (some (S.conv a)) η ε
  identity : ∀ (i : ι) (ε η : Bit),
    allowed (i := i) (j := i) none ε η ↔ ε = η ∧ validBit i ε

namespace MaskData
variable {S} (M : MaskData S)
def GlobalMarking (mark : Sigma X → Bit) : Prop :=
  (∀ p, M.validBit p.1 (mark p)) ∧
  ∀ (p q : Sigma X), M.allowed (S.colour p.2 q.2) (mark p) (mark q)

def LocalLegal {V : Type z} (D : PartialDiagram S V) (bits : V → Bit) : Prop :=
  (∀ x, M.validBit (D.vertexSort x) (bits x)) ∧
  ∀ x y h a, D.edge x y h = some a → M.allowed (some a) (bits x) (bits y)

/-- The finite pointwise seed theorem, including repeated quotient classes.
It is supplied from the accepted free-action seed extension, not marked AP. -/
def FiniteSeedExtension : Prop :=
  ∀ {V : Type (max u v)} [Finite V] (sort : V → ι)
    (point : ∀ x, X (sort x)) (bits : V → Bit),
    (∀ x, M.validBit (sort x) (bits x)) →
    (∀ x y, M.allowed (S.colour (point x) (point y)) (bits x) (bits y)) →
    ∃ mark, M.GlobalMarking mark ∧ ∀ x, mark ⟨sort x,point x⟩ = bits x

/-- The two source algebraic conclusions used by path supports and finite
completion. All products and intersections include the original diagonal. -/
structure Calculus : Prop where
  totality : ∀ {i j k : ι} (a : Option (S.Atom i j))
    (b : Option (S.Atom j k)) (ε η θ : Bit),
    M.validBit i ε → M.validBit j η → M.validBit k θ →
    M.allowed a ε η → M.allowed b η θ →
    TRel.Nonempty (S.rawAtomRel a) → TRel.Nonempty (S.rawAtomRel b) →
    ∃ (x : X i) (z : X k),
      TRel.comp (S.rawAtomRel a) (S.rawAtomRel b) x z ∧
      M.allowed (S.colour x z) ε θ
  primality : ∀ {i j : ι} (D : List (RawExact.NonemptyExact S i j))
    (ε η : Bit), M.validBit i ε → M.validBit j η →
    TRel.Nonempty (fun x y => ∀ d ∈ D, RawExact.evaluate S d.words x y) →
    (∀ d ∈ D, ∃ (x : X i) (y : X j),
      RawExact.evaluate S d.words x y ∧ M.allowed (S.colour x y) ε η) →
    ∃ (x : X i) (y : X j),
      (∀ d ∈ D, RawExact.evaluate S d.words x y) ∧
      M.allowed (S.colour x y) ε η

end MaskData
end CCO.APCharacter
