import Mathlib.GroupTheory.Perm.Basic
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Data.Setoid.Basic
import Mathlib.Order.Cover
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Data.Fintype.Perm

/-! C45 is an actual two-element permutation group action, with one fixed
point. It has a genuine invariant-equivalence cover whose relative class
counts vary. No CCO-source claim is made about this action. -/
namespace CCO.FiniteFibres.Boundaries.Nontransitive

abbrev Point := Fin 3
def flip : Equiv.Perm Point := Equiv.swap 0 1
abbrev G := Subgroup.zpowers flip

theorem flip_square : flip^2 = 1 := by
  apply Equiv.ext
  intro x
  simp [flip,pow_two]

theorem flip_nonidentity : flip ≠ 1 := by
  intro he
  have hh := congrArg (fun g : Equiv.Perm Point => g 0) he
  have hn : (1 : Point) ≠ 0 := by decide
  exact hn (by simpa [flip] using hh)

theorem group_card : Nat.card G = 2 := by
  letI : Fact (Nat.Prime 2) := ⟨by decide⟩
  calc
    Nat.card G = Nat.card (Fin (orderOf flip)) :=
      Nat.card_congr (finEquivZPowers (isOfFinOrder_of_finite flip)).symm
    _ = orderOf flip := Nat.card_fin _
    _ = 2 := orderOf_eq_prime flip_square flip_nonidentity

def fixesTwo : Subgroup (Equiv.Perm Point) where
  carrier := {g | g 2 = 2}
  one_mem' := rfl
  mul_mem' := by intro g h hg hh; change g (h 2) = 2; rw [hh,hg]
  inv_mem' := by
    intro g hg
    change g.symm 2 = 2
    have h := congrArg g.symm hg
    simpa only [Equiv.symm_apply_apply] using h.symm

theorem group_fixes_two (g : G) : g.val 2 = 2 := by
  have hle : G ≤ fixesTwo := Subgroup.zpowers_le.mpr (by
    change (Equiv.swap (0 : Point) 1) 2 = 2
    exact Equiv.swap_apply_of_ne_of_ne (by decide) (by decide))
  exact hle g.property

theorem group_moves_zero : ∃ g : G, g • (0 : Point) = 1 := by
  refine ⟨⟨flip,Subgroup.mem_zpowers flip⟩,?_⟩
  change (Equiv.swap (0 : Point) 1) 0 = 1
  exact Equiv.swap_apply_left _ _

theorem not_transitive : ¬∀ x y : Point, ∃ g : G, g • x = y := by
  intro h
  obtain ⟨g,hg⟩ := h 2 0
  have he : (2 : Point) = 0 := (group_fixes_two g).symm.trans hg
  exact (by decide : (2 : Point) ≠ 0) he

def coarse : Setoid Point where
  r x y := x = 2 ↔ y = 2
  iseqv := ⟨fun _ => Iff.rfl,fun h => h.symm,fun h k => h.trans k⟩

instance coarseDecidable : DecidableRel coarse.r :=
  fun x y => inferInstanceAs (Decidable (x = 2 ↔ y = 2))

theorem coarse_invariant (g : G) (x y : Point) :
    coarse (g • x) (g • y) ↔ coarse x y := by
  have hx : g.val x = 2 ↔ x = 2 := by
    have hh : g.val x = g.val 2 ↔ x = 2 := g.val.injective.eq_iff
    simpa only [group_fixes_two g] using hh
  have hy : g.val y = 2 ↔ y = 2 := by
    have hh : g.val y = g.val 2 ↔ y = 2 := g.val.injective.eq_iff
    simpa only [group_fixes_two g] using hh
  change (g.val x = 2 ↔ g.val y = 2) ↔ (x = 2 ↔ y = 2)
  rw [hx,hy]

theorem coarse_cover : (⊥ : Setoid Point) ⋖ coarse := by
  apply covBy_iff_lt_and_eq_or_eq.mpr
  constructor
  · refine lt_of_le_of_ne bot_le ?_
    intro he
    have hh : coarse 0 1 := by change ((0 : Point) = 2 ↔ (1 : Point) = 2); decide
    rw [←he] at hh
    have hn : (0 : Point) ≠ 1 := by decide
    exact hn hh
  · intro E _ hE
    by_cases h01 : E 0 1
    · right
      apply Setoid.ext
      intro x y
      constructor
      · exact fun h => hE h
      · intro h
        change (x = 2 ↔ y = 2) at h
        fin_cases x <;> fin_cases y
        all_goals first | exact E.refl _ | exact h01 | exact E.symm h01 | norm_num at h
    · left
      apply Setoid.ext
      intro x y
      constructor
      · intro h
        have hc : (x = 2 ↔ y = 2) := hE h
        change x = y
        fin_cases x <;> fin_cases y
        all_goals first | rfl | exact (h01 h).elim | exact (h01 (E.symm h)).elim | norm_num at hc
      · intro h
        change x = y at h
        exact h ▸ E.refl x

theorem class_zero_card : Fintype.card {x : Point // coarse x 0} = 2 := by decide
theorem class_two_card : Fintype.card {x : Point // coarse x 2} = 1 := by decide

/-- The actual quotient by the restricted LOWER equivalence. Since the
lower relation is logical equality, this is canonically the point class. -/
noncomputable def localIndex (a : Point) : ℕ :=
  Nat.card (Quotient (⊥ : Setoid {x : Point // coarse x a}))

theorem localIndex_eq (a : Point) :
    localIndex a = Fintype.card {x : Point // coarse x a} := by
  rw [localIndex,Nat.card_congr Setoid.quotientBotEquiv,Nat.card_eq_fintype_card]

theorem relative_indices_differ : localIndex 0 = 2 ∧ localIndex 2 = 1 := by
  rw [localIndex_eq,localIndex_eq,class_zero_card,class_two_card]
  exact ⟨rfl,rfl⟩

/-- For the lower equality relation, its classes inside a coarse class are
literally those points. Thus no uniform relative index exists at this cover. -/
theorem cover_counts_nonuniform :
    (⊥ : Setoid Point) ⋖ coarse ∧
    Fintype.card {x : Point // coarse x 0} = 2 ∧
    Fintype.card {x : Point // coarse x 2} = 1 :=
  ⟨coarse_cover,class_zero_card,class_two_card⟩

end CCO.FiniteFibres.Boundaries.Nontransitive
