import Mathlib.ModelTheory.Semantics
import Mathlib.Algebra.Group.TypeTags.Basic
import Mathlib.Algebra.Group.Action.Defs
import Mathlib.Data.Int.ModEq
import Mathlib.Logic.Equiv.Basic

/-!
# C45: translation invariance does not imply original-language definability

The original structure is the pure equality structure on the integers. The
translation subgroup acts transitively and preserves parity, but a permutation
of the same pure equality structure destroys parity. The nondefinability
statement quantifies over actual Mathlib first-order formulas, with arbitrary
quantifier depth, and no parameters. This example is outside the finite named
pair-orbital context used by the positive definability result.
-/

namespace CCO.QuotientTransport.Boundaries.NonDefinability

open FirstOrder FirstOrder.Language

/-- The actual parity equivalence, including its real diagonal. -/
def parity : Setoid ℤ := Setoid.ker (fun x : ℤ => x % 2)

/-- Translation preserves the actual parity equivalence. -/
theorem parity_translate (k x y : ℤ) (h : parity x y) :
    parity (k + x) (k + y) := by
  change x % 2 = y % 2 at h
  change (k + x) % 2 = (k + y) % 2
  calc
    (k + x) % 2 = (k % 2 + x % 2) % 2 := Int.add_emod k x 2
    _ = (k % 2 + y % 2) % 2 := congrArg (fun z : ℤ => (k % 2 + z) % 2) h
    _ = (k + y) % 2 := (Int.add_emod k y 2).symm

/-- Every point is reached from every other by a literal translation. -/
theorem translation_transitive (x y : ℤ) : ∃ k : ℤ, k + x = y :=
  ⟨y - x, sub_add_cancel y x⟩

/-- The group of literal integer translations, written multiplicatively. -/
instance translationAction : MulAction (Multiplicative ℤ) ℤ where
  smul k x := k.toAdd + x
  one_smul x := zero_add x
  mul_smul g h x := add_assoc g.toAdd h.toAdd x

theorem parity_group_invariant (g : Multiplicative ℤ) (x y : ℤ)
    (h : parity x y) : parity (g • x) (g • y) := parity_translate g.toAdd x y h

theorem translation_group_transitive (x y : ℤ) :
    ∃ g : Multiplicative ℤ, g • x = y :=
  ⟨Multiplicative.ofAdd (y - x), sub_add_cancel y x⟩

instance pureEqualityStructure : Language.empty.Structure ℤ := Language.emptyStructure

/-- Parameter-free definability in the actual empty first-order language. -/
def PureEqualityDefinable (R : ℤ → ℤ → Prop) : Prop :=
  ∃ φ : Language.empty.Formula (Fin 2),
    ∀ v : Fin 2 → ℤ, φ.Realize v ↔ R (v 0) (v 1)

/-- All pure-equality formulas, including quantified formulas, are invariant
under every permutation. This uses the actual first-order semantics theorem. -/
theorem formula_permutation_invariant (φ : Language.empty.Formula (Fin 2))
    (e : Equiv.Perm ℤ) (v : Fin 2 → ℤ) :
    φ.Realize (e ∘ v) ↔ φ.Realize v :=
  StrongHomClass.realize_formula e φ

/-- Swapping 1 and 2 is an automorphism of pure equality but destroys parity:
the old pair (0,2) is equivalent and the new pair (0,1) is not. -/
theorem swap_destroys_parity :
    parity 0 2 ∧ ¬ parity ((Equiv.swap (1 : ℤ) 2) 0) ((Equiv.swap (1 : ℤ) 2) 2) := by
  constructor
  · change (0 : ℤ) % 2 = 2 % 2
    decide
  · have h0 : (Equiv.swap (1 : ℤ) 2) 0 = 0 :=
      Equiv.swap_apply_of_ne_of_ne (by decide) (by decide)
    rw [h0, Equiv.swap_apply_right]
    change ¬ (0 : ℤ) % 2 = 1 % 2
    decide

/-- C45: the actual translation-invariant equivalence is not first-order
definable in its original pure equality structure. -/
theorem parity_not_definable : ¬ PureEqualityDefinable parity := by
  rintro ⟨φ, hφ⟩
  let v : Fin 2 → ℤ := fun i => if i = 0 then 0 else 2
  let e : Equiv.Perm ℤ := Equiv.swap 1 2
  have hOld : φ.Realize v := (hφ v).mpr swap_destroys_parity.1
  have hNew := (hφ (e ∘ v)).mp ((formula_permutation_invariant φ e v).mpr hOld)
  exact swap_destroys_parity.2 hNew

/-- With the actual identity relation as R, transporting parity returns parity.
The kernel hypothesis is satisfied, so invariant transport still cannot create
a formula that was absent from the original language. -/
theorem identity_transport_parity (x y : ℤ) :
    (∃ a b : ℤ, a = x ∧ parity a b ∧ b = y) ↔ parity x y := by
  constructor
  · rintro ⟨a, b, rfl, hab, rfl⟩
    exact hab
  · intro h
    exact ⟨x, y, rfl, h, rfl⟩

end CCO.QuotientTransport.Boundaries.NonDefinability
