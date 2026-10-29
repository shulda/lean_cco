import CCO.ProfileHelly.Paths
import Mathlib.Data.Sym.Card

/-! One actual edge assignment on the SAME formal vertex set. Both
orientations are written with literal converses; every old record remains. -/
universe u v z
namespace CCO.ProfileHelly.Network
variable {ι : Type u} {T : Table.{u,v} ι} {V : Type z} {sort : V → ι}
variable (D : Network T sort)

def castAtom {i j k l : ι} (h : i = k) (h' : j = l) (a : T.Atom i j) : T.Atom k l := by
  cases h
  cases h'
  exact a

@[simp] theorem castAtom_refl {i j : ι} (a : T.Atom i j) :
    castAtom (T := T) rfl rfl a = a := rfl

noncomputable def filledEdge (x y : V) (a : T.Atom (sort x) (sort y))
    (p q : V) : Option (T.Atom (sort p) (sort q)) := by
  classical
  exact if h : p = x ∧ q = y then
      some (castAtom (congrArg sort h.1).symm (congrArg sort h.2).symm a)
    else if h : p = y ∧ q = x then
      some (castAtom (congrArg sort h.1).symm (congrArg sort h.2).symm (T.conv a))
    else D.edge p q

noncomputable def fill (x y : V) (hne : x ≠ y) (a : T.Atom (sort x) (sort y)) :
    Network T sort where
  edge := D.filledEdge x y a
  diagonal := by
    intro p
    have h₁ : ¬(p = x ∧ p = y) := fun h => hne (h.1.symm.trans h.2)
    have h₂ : ¬(p = y ∧ p = x) := fun h => hne (h.2.symm.trans h.1)
    simp [filledEdge,h₁,h₂,D.diagonal]
  edge_reverse := by
    classical
    intro p q
    by_cases h : p = x ∧ q = y
    · rcases h with ⟨hp,hq⟩
      subst p
      subst q
      simp [filledEdge,hne,Ne.symm hne,T.conv_invol]
    · by_cases h' : p = y ∧ q = x
      · rcases h' with ⟨hp,hq⟩
        subst p
        subst q
        simp [filledEdge,hne,Ne.symm hne]
      · have h₁ : ¬(q = x ∧ p = y) := fun hh => h' ⟨hh.2,hh.1⟩
        have h₂ : ¬(q = y ∧ p = x) := fun hh => h ⟨hh.2,hh.1⟩
        simp [filledEdge,h,h',h₁,h₂,D.edge_reverse]

@[simp] theorem fill_forward (x y : V) (hne : x ≠ y) (a : T.Atom (sort x) (sort y)) :
    (D.fill x y hne a).edge x y = some a := by
  simp [fill,filledEdge]

@[simp] theorem fill_backward (x y : V) (hne : x ≠ y) (a : T.Atom (sort x) (sort y)) :
    (D.fill x y hne a).edge y x = some (T.conv a) := by
  simp [fill,filledEdge,Ne.symm hne]

theorem fill_other (x y : V) (hne : x ≠ y) (a : T.Atom (sort x) (sort y))
    (p q : V) (h : ¬(p = x ∧ q = y)) (h' : ¬(p = y ∧ q = x)) :
    (D.fill x y hne a).edge p q = D.edge p q := by
  simp [fill,filledEdge,h,h']

theorem reverse_missing (x y : V) (h : D.edge x y = none) : D.edge y x = none := by
  have hh := D.edge_reverse x y
  rw [h] at hh
  exact Option.map_eq_none_iff.mp hh

theorem fill_extends (x y : V) (hne : x ≠ y) (a : T.Atom (sort x) (sort y))
    (hmissing : D.edge x y = none) : D.Extends (D.fill x y hne a) := by
  intro p q b hb
  by_cases h : p = x ∧ q = y
  · rcases h with ⟨hp,hq⟩
    subst p
    subst q
    rw [hmissing] at hb
    cases hb
  · by_cases h' : p = y ∧ q = x
    · rcases h' with ⟨hp,hq⟩
      subst p
      subst q
      rw [D.reverse_missing x y hmissing] at hb
      cases hb
    · exact (D.fill_other x y hne a p q h h').trans hb

end CCO.ProfileHelly.Network
