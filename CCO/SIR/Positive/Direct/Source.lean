import CCO.ActionBridge
import Mathlib.Data.Bool.Basic
import Mathlib.Data.Fintype.Option
import Mathlib.Tactic.FinCases

/-! The original real language has precisely the three symmetric diversity
colours e,d,n. Neither a parent nor a sheet is named by the language. -/
namespace CCO.SIR.Positive.Direct

abbrev Point := ℕ × Bool × ℕ

inductive Colour | e | d | n deriving DecidableEq

instance : Fintype Colour := ⟨{.e,.d,.n}, by intro a; cases a <;> simp⟩

abbrev parent (x : Point) : ℕ := x.1
abbrev sheet (x : Point) : Bool := x.2.1
abbrev index (x : Point) : ℕ := x.2.2

def F (x y : Point) : Prop := parent x = parent y
def E (x y : Point) : Prop := F x y ∧ sheet x = sheet y

instance : DecidableRel F := fun _ _ => inferInstanceAs (Decidable (_ = _))
instance : DecidableRel E := fun _ _ => inferInstanceAs (Decidable (_ ∧ _))

def colour (x y : Point) : Option Colour :=
  if x = y then none else if F x y then
    if sheet x = sheet y then some .e else some .d
  else some .n

@[simp] theorem colour_none (x y : Point) : colour x y = none ↔ x = y := by
  simp [colour]; split_ifs <;> simp_all

@[simp] theorem colour_e (x y : Point) :
    colour x y = some .e ↔ x ≠ y ∧ E x y := by
  simp [colour, E]; split_ifs <;> simp_all

@[simp] theorem colour_d (x y : Point) :
    colour x y = some .d ↔ F x y ∧ sheet x ≠ sheet y := by
  unfold colour
  split_ifs with h hF hS <;> simp_all [F]

@[simp] theorem colour_n (x y : Point) :
    colour x y = some .n ↔ ¬ F x y := by
  unfold colour
  split_ifs with h hF hS <;> simp_all [F]

theorem colour_symm (x y : Point) : colour x y = colour y x := by
  unfold colour F
  simp only [eq_comm]
  rfl

@[simp] theorem E_self (x : Point) : E x x := ⟨rfl, rfl⟩
@[simp] theorem F_self (x : Point) : F x x := rfl

def parentSetoid : Setoid Point :=
  ⟨F, ⟨fun _ => rfl, Eq.symm, Eq.trans⟩⟩
def sheetSetoid : Setoid Point :=
  ⟨E, ⟨E_self, fun h => ⟨h.1.symm, h.2.symm⟩,
    fun h k => ⟨h.1.trans k.1, h.2.trans k.2⟩⟩⟩

/-- Equality-inclusive E and F are recovered from the original atomic colour. -/
theorem E_iff_colour (x y : Point) :
    E x y ↔ colour x y = none ∨ colour x y = some .e := by
  rw [colour_none, colour_e]
  constructor
  · intro h; by_cases he : x = y
    · exact Or.inl he
    · exact Or.inr ⟨he, h⟩
  · rintro (rfl | h); exact E_self _; exact h.2

theorem F_iff_colour (x y : Point) :
    F x y ↔ colour x y ≠ some .n := by simp

theorem coordinates_of_colour_eq {x y x' y' : Point}
    (h : colour x y = colour x' y') :
    (x = y ↔ x' = y') ∧ (F x y ↔ F x' y') ∧ (E x y ↔ E x' y') := by
  constructor
  · simpa only [← colour_none, h]
  constructor
  · simp only [F_iff_colour, h]
  · simp only [E_iff_colour, h]

/-- A one-sort source on the literal carrier ℕ×Bool×ℕ. -/
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
    change colour x y = some a ↔ colour y x = some a
    rw [colour_symm]
  realized := by
    intro i j a
    cases a with
    | e => exact ⟨(0,false,0),(0,false,1),by decide⟩
    | d => exact ⟨(0,false,0),(0,true,0),by decide⟩
    | n => exact ⟨(0,false,0),(1,false,0),by decide⟩

@[simp] theorem source_colour {i j : Unit} (x y : Point) :
    source.colour (i := i) (j := j) x y = colour x y := rfl

end CCO.SIR.Positive.Direct
