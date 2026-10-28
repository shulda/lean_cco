import CCO.SIR.Positive.Direct.Source
import CCO.SIR.Positive.Direct.SignedWalk
import CCO.SIR.Positive.Direct.CycleWalk
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

/-! The signed e/d graph of an actual partial diagram in the three-colour
language. These definitions use only the specified original edges. -/

universe z

namespace CCO.SIR.Positive.Direct

variable {V : Type z} (D : PartialDiagram source V)

def edGraph : SimpleGraph V where
  Adj x y := ∃ h : x ≠ y, D.edge x y h = some .e ∨ D.edge x y h = some .d
  symm := ⟨by
    intro x y hxy
    obtain ⟨h, he | hd⟩ := hxy
    · exact ⟨h.symm, Or.inl ((D.edge_reverse x y h .e).mp he)⟩
    · exact ⟨h.symm, Or.inr ((D.edge_reverse x y h .d).mp hd)⟩⟩
  loopless := ⟨by intro x h; exact h.choose rfl⟩

def specifiedGraph : SimpleGraph V where
  Adj x y := ∃ (h : x ≠ y), ∃ a, D.edge x y h = some a
  symm := ⟨by
    rintro x y ⟨h,a,ha⟩
    exact ⟨h.symm,a,(D.edge_reverse x y h a).mp ha⟩⟩
  loopless := ⟨by intro x h; exact h.choose rfl⟩

theorem edGraph_le_specifiedGraph : edGraph D ≤ specifiedGraph D := by
  rintro x y ⟨h,he | hd⟩
  · exact ⟨h,.e,he⟩
  · exact ⟨h,.d,hd⟩

noncomputable def sign (x y : V) : Bool :=
  @decide (∃ h : x ≠ y, D.edge x y h = some .d) (Classical.propDecidable _)

theorem sign_symm (x y : V) : sign D x y = sign D y x := by
  classical
  have hh : (∃ h : x ≠ y, D.edge x y h = some .d) ↔
      (∃ h : y ≠ x, D.edge y x h = some .d) := by
    constructor <;> rintro ⟨h,hh⟩
    · exact ⟨h.symm,(D.edge_reverse x y h .d).mp hh⟩
    · exact ⟨h.symm,(D.edge_reverse y x h .d).mp hh⟩
  exact decide_eq_decide.mpr hh

theorem sign_e {x y : V} (h : x ≠ y) (he : D.edge x y h = some .e) :
    sign D x y = false := by
  have hn : ¬ ∃ h : x ≠ y, D.edge x y h = some .d := by
    rintro ⟨h',hd⟩
    rw [he] at hd
    cases hd
  simpa [sign] using hn

theorem sign_d {x y : V} (h : x ≠ y) (hd : D.edge x y h = some .d) :
    sign D x y = true := by
  have hh : ∃ h : x ≠ y, D.edge x y h = some .d := ⟨h,hd⟩
  simpa [sign] using hh

theorem sign_of_realized_edge {x y : V} (hadj : (edGraph D).Adj x y)
    (p q : Point)
    (hreal : ∀ (h : x ≠ y) a, D.edge x y h = some a → colour p q = some a) :
    sign D x y = (sheet p ^^ sheet q) := by
  obtain ⟨h,he | hd⟩ := hadj
  · rw [sign_e D h he]
    have hh := (colour_e p q).mp (hreal h .e he)
    rw [hh.2.2]
    simp
  · rw [sign_d D h hd]
    have hh := (colour_d p q).mp (hreal h .d hd)
    cases hp : sheet p <;> cases hq : sheet q <;> simp_all

theorem parent_of_realized_edge {x y : V} (hadj : (edGraph D).Adj x y)
    (p q : Point)
    (hreal : ∀ (h : x ≠ y) a, D.edge x y h = some a → colour p q = some a) :
    parent p = parent q := by
  obtain ⟨h,he | hd⟩ := hadj
  · exact ((colour_e p q).mp (hreal h .e he)).2.1
  · exact ((colour_d p q).mp (hreal h .d hd)).1

end CCO.SIR.Positive.Direct
