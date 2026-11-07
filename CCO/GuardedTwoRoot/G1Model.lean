import CCO.Atomic
import Mathlib.Algebra.Group.Subgroup.Actions
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Tactic.FinCases

/-! The source14 FG1 diagnostic is the literal infinite
blocks × Bool × clones source. Its THREE old diversity atoms are all
retained: p = same block/bit, q = same block/opposite bit, r = different
blocks. Logical real equality is none, never a fourth fine atom. -/

namespace CCO.GuardedTwoRoot.G1

abbrev Real := (ℕ × Bool) × ℕ
abbrev Atom := Fin 3
abbrev p : Atom := 0
abbrev q : Atom := 1
abbrev r : Atom := 2

def block (x : Real) : ℕ := x.1.1
def bit (x : Real) : Bool := x.1.2
def clone (x : Real) : ℕ := x.2

def colour (x y : Real) : Option Atom :=
  if x = y then none else if block x = block y then
    some (if bit x = bit y then p else q) else some r

theorem colour_none (x y : Real) : colour x y = none ↔ x = y := by
  by_cases h : x = y <;> by_cases hb : block x = block y <;>
    by_cases hc : bit x = bit y <;> simp [colour,h,hb,hc,p,q,r]

theorem colour_p (x y : Real) :
    colour x y = some p ↔ x ≠ y ∧ block x = block y ∧ bit x = bit y := by
  by_cases h : x = y <;> by_cases hb : block x = block y <;>
    by_cases hc : bit x = bit y <;> simp [colour,h,hb,hc,p,q,r]

theorem colour_q (x y : Real) :
    colour x y = some q ↔ block x = block y ∧ bit x ≠ bit y := by
  by_cases h : x = y
  · subst y
    simp [colour]
  · by_cases hb : block x = block y <;> by_cases hc : bit x = bit y <;>
      simp [colour,h,hb,hc,p,q,r]

theorem colour_r (x y : Real) : colour x y = some r ↔ block x ≠ block y := by
  by_cases h : x = y
  · subst y
    simp [colour]
  · by_cases hb : block x = block y <;> by_cases hc : bit x = bit y <;>
      simp [colour,h,hb,hc,p,q,r]

theorem colour_symm (x y : Real) : colour x y = colour y x := by
  cases h : colour x y with
  | none =>
    have he := (colour_none x y).mp h
    subst y
    exact ((colour_none x x).mpr rfl).symm
  | some a =>
    fin_cases a
    · obtain ⟨hne,hb,hc⟩ := (colour_p x y).mp h
      exact ((colour_p y x).mpr ⟨Ne.symm hne,hb.symm,hc.symm⟩).symm
    · obtain ⟨hb,hc⟩ := (colour_q x y).mp h
      exact ((colour_q y x).mpr ⟨hb.symm,Ne.symm hc⟩).symm
    · exact ((colour_r y x).mpr (Ne.symm ((colour_r x y).mp h))).symm

def source : AtomicSource Unit (fun _ => Real) where
  Atom := fun _ _ => Atom
  finiteSort := inferInstance
  finiteAtom := fun _ _ => inferInstance
  nonemptySort := fun _ => ⟨((0,false),0)⟩
  conv := id
  conv_invol := fun _ => rfl
  symmetricLoop := fun _ => rfl
  colour := colour
  colour_none_iff := by
    intro i j x y
    cases i; cases j
    simpa only [Sigma.mk.injEq,heq_eq_eq,true_and] using colour_none x y
  colour_swap x y a := congrArg (· = some a) (colour_symm x y) |>.to_iff
  realized := by
    intro i j a
    fin_cases a
    · exact ⟨((0,false),0),((0,false),1),by decide⟩
    · exact ⟨((0,false),0),((0,true),0),by decide⟩
    · exact ⟨((0,false),0),((1,false),0),by decide⟩

theorem block_eq_iff (x y : Real) :
    block x = block y ↔ colour x y = none ∨ colour x y = some p ∨ colour x y = some q := by
  by_cases h : x = y
  · subst y; simp [colour]
  · by_cases hb : block x = block y <;> by_cases hc : bit x = bit y <;>
      simp [colour,h,hb,hc,p,q,r]

theorem fine_eq_iff (x y : Real) :
    (block x = block y ∧ bit x = bit y) ↔ colour x y = none ∨ colour x y = some p := by
  by_cases h : x = y
  · subst y; simp [colour]
  · by_cases hb : block x = block y <;> by_cases hc : bit x = bit y <;>
      simp [colour,h,hb,hc,p,q,r]

theorem block_of_colour {x y x' y' : Real} (h : colour x y = colour x' y') :
    block x = block y ↔ block x' = block y' := by
  rw [block_eq_iff,block_eq_iff,h]

theorem fine_of_colour {x y x' y' : Real} (h : colour x y = colour x' y') :
    (block x = block y ∧ bit x = bit y) ↔
      (block x' = block y' ∧ bit x' = bit y') := by
  rw [fine_eq_iff,fine_eq_iff,h]

def autGroup : Subgroup (Equiv.Perm Real) where
  carrier := {g | ∀ x y, colour (g x) (g y) = colour x y}
  one_mem' := by intro x y; rfl
  mul_mem' := by intro g h hg hh x y; exact (hg (h x) (h y)).trans (hh x y)
  inv_mem' := by
    intro g hg x y
    have h := hg (g⁻¹ x) (g⁻¹ y)
    simpa using h.symm

abbrev Aut := autGroup

instance autAction : MulAction Aut Real where
  smul g x := g.val x
  one_smul _ := rfl
  mul_smul _ _ _ := rfl

theorem aut_colour (g : Aut) (x y : Real) : colour (g • x) (g • y) = colour x y :=
  g.property x y

end CCO.GuardedTwoRoot.G1
