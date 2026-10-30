import CCO.ResetOrder.Hierarchy.Lattice
import Mathlib.Data.Setoid.Basic

/-! Faithful equivalence lattices and actual quotient maps. -/
universe u v
namespace CCO.ResetOrder.Hierarchy

structure EquivalenceLattice (L : Type u) [Lattice L] [OrderTop L] (V : Type v) where
  relation : L → Setoid V
  faithful : Function.Injective relation
  inf_eq : ∀ a b, relation (a ⊓ b) = relation a ⊓ relation b
  top_eq : relation ⊤ = ⊤

namespace EquivalenceLattice
variable {L : Type u} [Lattice L] [OrderTop L] [Fintype L] {V : Type v}
variable (R : EquivalenceLattice L V)

theorem mono {j l : L} (h : j ≤ l) : R.relation j ≤ R.relation l := by
  have hm := R.inf_eq j l
  rw [inf_eq_left.2 h] at hm
  exact inf_eq_left.1 hm.symm

theorem inf_rel (s : Finset L) (x y : V) :
    (R.relation (s.inf id)).r x y ↔ ∀ l ∈ s, (R.relation l).r x y := by
  classical
  induction s using Finset.induction with
  | empty =>
    change (R.relation ⊤).r x y ↔ ∀ l ∈ (∅ : Finset L), (R.relation l).r x y
    rw [R.top_eq]
    simp
  | insert l s hl ih =>
    rw [Finset.inf_insert, R.inf_eq]
    change ((R.relation l).r x y ∧ (R.relation (s.inf id)).r x y) ↔ _
    rw [ih]
    simp

theorem parent_rel_iff (j : L) (x y : V) :
    (R.relation (miParent j)).r x y ↔ ∀ l, j < l → InfIrred l → (R.relation l).r x y := by
  rw [← strictCoarserMI_inf j, R.inf_rel]
  simp [strictCoarserMI]

def Point (j : L) := Quotient (R.relation j)

def up {j l : L} (h : j ≤ l) : R.Point j → R.Point l :=
  Quotient.map id (fun _ _ hxy => R.mono h hxy)

@[simp] theorem up_mk {j l : L} (h : j ≤ l) (x : V) :
    R.up h (Quotient.mk _ x) = Quotient.mk _ x := rfl

@[simp] theorem up_refl (j : L) (x : R.Point j) : R.up (le_refl j) x = x := by
  induction x using Quotient.inductionOn
  rfl

@[simp] theorem up_comp {j l m : L} (hjl : j ≤ l) (hlm : l ≤ m) (x : R.Point j) :
    R.up hlm (R.up hjl x) = R.up (hjl.trans hlm) x := by
  induction x using Quotient.inductionOn
  rfl

def CoarserMI (j : L) := {l : L // j < l ∧ InfIrred l}

def key (j : L) (x : R.Point j) : (l : CoarserMI j) → R.Point l.val :=
  fun l => R.up l.property.1.le x

theorem key_eq_parent_iff (j : L) (x y : R.Point j) :
    R.key j x = R.key j y ↔ R.up (le_miParent j) x = R.up (le_miParent j) y := by
  induction x using Quotient.inductionOn with | _ x =>
    induction y using Quotient.inductionOn with | _ y =>
      constructor
      · intro h
        apply Quotient.sound
        apply (R.parent_rel_iff j x y).2
        intro l hjl hmi
        exact Quotient.exact (congrFun h ⟨l, hjl, hmi⟩)
      · intro h
        funext l
        apply Quotient.sound
        exact (R.parent_rel_iff j x y).1 (Quotient.exact h) l.val l.property.1 l.property.2

theorem top_parent_constant (j : L) (hj : miParent j = ⊤) (x y : R.Point j) :
    R.up (le_miParent j) x = R.up (le_miParent j) y := by
  induction x using Quotient.inductionOn with | _ x =>
    induction y using Quotient.inductionOn with | _ y =>
      apply Quotient.sound
      rw [hj, R.top_eq]
      trivial
end EquivalenceLattice
end CCO.ResetOrder.Hierarchy
