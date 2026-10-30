import Mathlib.Basic.Finite.Set
import Mathlib.Logic.Relation
import Mathlib.Data.Set.Lattice.Indexed

/-! Elementary many-sorted partial-unary structures for the full tuple code.
There are no nullary or higher-arity relation symbols. -/
universe u v w z
namespace CCO.FullCode

structure Language where
  Sorts : Type u
  Func : Type u
  Unary : Type u
  Binary : Type u
  input : Func → Sorts
  output : Func → Sorts
  unarySort : Unary → Sorts
  leftSort : Binary → Sorts
  rightSort : Binary → Sorts
  finiteSort : Finite Sorts
  finiteFunc : Finite Func
  finiteUnary : Finite Unary
  finiteBinary : Finite Binary

attribute [instance] Language.finiteSort Language.finiteFunc
  Language.finiteUnary Language.finiteBinary

structure Structure (L : Language.{u}) (V : Type v) where
  sort : V → L.Sorts
  func : L.Func → V → Set V
  functional : ∀ F x y z, y ∈ func F x → z ∈ func F x → y = z
  func_sorted : ∀ F x y, y ∈ func F x → sort x = L.input F ∧ sort y = L.output F
  unary : L.Unary → V → Prop
  unary_sorted : ∀ U x, unary U x → sort x = L.unarySort U
  binary : L.Binary → V → V → Prop
  binary_sorted : ∀ R x y, binary R x y → sort x = L.leftSort R ∧ sort y = L.rightSort R

namespace Structure
variable {L : Language.{u}} {V : Type v} {W : Type w} {Z : Type z}

def IsClosed (C : Structure L V) (S : Set V) : Prop :=
  ∀ F x, x ∈ S → C.func F x ⊆ S

structure Embedding (C : Structure L V) (D : Structure L W) where
  point : V → W
  injective : Function.Injective point
  sort_eq : ∀ x, D.sort (point x) = C.sort x
  map_func : ∀ F x y, y ∈ C.func F x → point y ∈ D.func F (point x)
  reflect_func : ∀ F x y, y ∈ D.func F (point x) → ∃ z, z ∈ C.func F x ∧ point z = y
  unary_iff : ∀ U x, D.unary U (point x) ↔ C.unary U x
  binary_iff : ∀ R x y, D.binary R (point x) (point y) ↔ C.binary R x y

@[ext] theorem Embedding.ext {C : Structure L V} {D : Structure L W}
    {f g : Embedding C D} (h : ∀ x, f.point x = g.point x) : f = g := by
  cases f; cases g
  have hp := funext h
  cases hp
  rfl

def Embedding.id (C : Structure L V) : Embedding C C where
  point x := x
  injective := Function.injective_id
  sort_eq _ := rfl
  map_func _ _ _ h := h
  reflect_func _ _ y h := ⟨y, h, rfl⟩
  unary_iff _ _ := Iff.rfl
  binary_iff _ _ _ := Iff.rfl

def Embedding.comp {C : Structure L V} {D : Structure L W} {E : Structure L Z}
    (g : Embedding D E) (f : Embedding C D) : Embedding C E where
  point := g.point ∘ f.point
  injective := g.injective.comp f.injective
  sort_eq x := (g.sort_eq _).trans (f.sort_eq x)
  map_func F x y h := g.map_func F _ _ (f.map_func F x y h)
  reflect_func F x y h := by
    obtain ⟨b, hb, hby⟩ := g.reflect_func F _ y h
    obtain ⟨a, ha, hab⟩ := f.reflect_func F x b hb
    exact ⟨a, ha, (congrArg g.point hab).trans hby⟩
  unary_iff U x := (g.unary_iff U _).trans (f.unary_iff U x)
  binary_iff R x y := (g.binary_iff R _ _).trans (f.binary_iff R x y)

def Step (C : Structure L V) (x y : V) : Prop := ∃ F, y ∈ C.func F x

def closure (C : Structure L V) (S : Set V) : Set V :=
  {y | ∃ x ∈ S, Relation.ReflTransGen C.Step x y}

theorem subset_closure (C : Structure L V) (S : Set V) : S ⊆ C.closure S := by
  intro x hx; exact ⟨x, hx, .refl⟩

theorem isClosed_closure (C : Structure L V) (S : Set V) : C.IsClosed (C.closure S) := by
  rintro F y ⟨x, hx, hxy⟩ z hz
  exact ⟨x, hx, hxy.tail ⟨F, hz⟩⟩

theorem closure_minimal (C : Structure L V) {S T : Set V}
    (hT : C.IsClosed T) (hST : S ⊆ T) : C.closure S ⊆ T := by
  rintro y ⟨x, hx, hxy⟩
  have hstart := hST hx
  induction hxy with
  | refl => exact hstart
  | tail h hstep ih =>
    obtain ⟨F, hF⟩ := hstep
    exact hT F _ ih hF

theorem closure_eq (C : Structure L V) {S : Set V} (hS : C.IsClosed S) :
    C.closure S = S := Set.Subset.antisymm
  (C.closure_minimal hS (Set.Subset.refl _)) (C.subset_closure S)

def induce (C : Structure L V) (S : Set V) (_hS : C.IsClosed S) : Structure L S where
  sort x := C.sort x.val
  func F x := {y | y.val ∈ C.func F x.val}
  functional F x y z hy hz := Subtype.ext (C.functional F x.val y.val z.val hy hz)
  func_sorted F x y hy := C.func_sorted F x.val y.val hy
  unary U x := C.unary U x.val
  unary_sorted U x hx := C.unary_sorted U x.val hx
  binary R x y := C.binary R x.val y.val
  binary_sorted R x y hxy := C.binary_sorted R x.val y.val hxy

def inclusion (C : Structure L V) (S : Set V) (hS : C.IsClosed S) :
    Embedding (C.induce S hS) C where
  point := Subtype.val
  injective := Subtype.val_injective
  sort_eq _ := rfl
  map_func _ _ _ h := h
  reflect_func F x y hy := ⟨⟨y, hS F x.val x.property hy⟩, hy, rfl⟩
  unary_iff _ _ := Iff.rfl
  binary_iff _ _ _ := Iff.rfl

theorem Embedding.range_closed {C : Structure L V} {D : Structure L W}
    (f : Embedding C D) : D.IsClosed (Set.range f.point) := by
  rintro F _ ⟨x, rfl⟩ y hy
  obtain ⟨z, _, rfl⟩ := f.reflect_func F x y hy
  exact ⟨z, rfl⟩

end Structure
end CCO.FullCode
