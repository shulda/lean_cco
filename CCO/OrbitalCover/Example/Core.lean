import CCO.Finite
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.CharP.Two
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Set.Countable

/-! The actual countably infinite nine-colour structure. Logical equality
is separate from the diversity colour `(some 0, some 0)` between clones. -/
namespace CCO.OrbitalCover.Example

abbrev Bit := ZMod 2
abbrev CoordColour := Option Bit
abbrev Colour := CoordColour × CoordColour

structure Point where
  u : ℕ
  v : ℕ
  p : Bit
  q : Bit
  n : ℕ
  deriving DecidableEq

instance : Countable Point := Function.Injective.countable
  (f := fun x : Point => (x.u, x.v, x.p, x.q, x.n)) (by
    intro x y h
    cases x; cases y
    simpa only [Prod.mk.injEq, Point.mk.injEq] using h)

instance : Inhabited Point := ⟨⟨0, 0, 0, 0, 0⟩⟩

def coordinateColour (b : ℕ) (p : Bit) (b' : ℕ) (p' : Bit) : CoordColour :=
  if b = b' then some (p + p') else none

def pattern (x y : Point) : Colour :=
  (coordinateColour x.u x.p y.u y.p, coordinateColour x.v x.q y.v y.q)

def colour (x y : Point) : Option Colour :=
  if x = y then none else some (pattern x y)

@[simp] theorem coordinateColour_self (b : ℕ) (p : Bit) :
    coordinateColour b p b p = some 0 := by
  simp [coordinateColour, CharTwo.add_self_eq_zero]

@[simp] theorem pattern_self (x : Point) : pattern x x = (some 0, some 0) := by
  simp [pattern]

theorem coordinateColour_symm (b b' : ℕ) (p p' : Bit) :
    coordinateColour b p b' p' = coordinateColour b' p' b p := by
  simp only [coordinateColour, eq_comm, add_comm]

theorem pattern_symm (x y : Point) : pattern x y = pattern y x := by
  simp only [pattern, coordinateColour_symm]

@[simp] theorem colour_none (x y : Point) : colour x y = none ↔ x = y := by
  simp [colour]

@[simp] theorem colour_some (x y : Point) (a : Colour) :
    colour x y = some a ↔ x ≠ y ∧ pattern x y = a := by
  by_cases h : x = y <;> simp [colour, h]

theorem colour_symm (x y : Point) : colour x y = colour y x := by
  simp only [colour, eq_comm, pattern_symm]

theorem pattern_of_colour {x y x' y' : Point}
    (h : colour x y = colour x' y') : pattern x y = pattern x' y' := by
  cases hc : colour x y with
  | none =>
    have he := (colour_none x y).mp hc
    have he' := (colour_none x' y').mp (h.symm.trans hc)
    subst y; subst y'
    simp
  | some a =>
    exact ((colour_some x y a).mp hc).2.trans
      ((colour_some x' y' a).mp (h.symm.trans hc)).2.symm

@[simp] theorem coordinateColour_isSome (b b' : ℕ) (p p' : Bit) :
    (coordinateColour b p b' p').isSome = true ↔ b = b' := by
  by_cases h : b = b' <;> simp [coordinateColour, h]

@[simp] theorem coordinateColour_some (b b' : ℕ) (p p' r : Bit) :
    coordinateColour b p b' p' = some r ↔ b = b' ∧ p + p' = r := by
  by_cases h : b = b' <;> simp [coordinateColour, h]

def source : AtomicSource Unit (fun _ => Point) where
  Atom := fun _ _ => Colour
  finiteSort := inferInstance
  finiteAtom := fun _ _ => inferInstance
  nonemptySort := fun _ => inferInstance
  conv := id
  conv_invol := fun _ => rfl
  symmetricLoop := fun _ => rfl
  colour := colour
  colour_none_iff := by
    intro i j x y
    cases i; cases j
    simpa using colour_none x y
  colour_swap := by
    intro i j x y a
    exact congrArg (· = some a) (colour_symm x y) |>.to_iff
  realized := by
    intro i j a
    let x : Point := ⟨0, 0, 0, 0, 0⟩
    let y : Point := ⟨if a.1.isSome then 0 else 1,
      if a.2.isSome then 0 else 1, a.1.getD 0, a.2.getD 0, 1⟩
    refine ⟨x, y, (colour_some x y a).mpr ⟨?_, ?_⟩⟩
    · intro h
      have hh := congrArg Point.n h
      change 0 = 1 at hh
      cases hh
    · rcases a with ⟨a, b⟩
      cases a <;> cases b <;> simp [x, y, pattern, coordinateColour]

@[simp] theorem source_colour {i j : Unit} (x y : Point) :
    source.colour (i := i) (j := j) x y = colour x y := rfl

theorem colour_card : Fintype.card Colour = 9 := by decide

end CCO.OrbitalCover.Example
