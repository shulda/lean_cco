import CCO.SafeReadings.ReturnNormalForm
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Logic.Function.Iterate
import Mathlib.Data.Finset.Lattice.Fold

/-! The actual finite pure action and optional converse clear after
2|Gamma| iterations. This is a group exponent argument, with no faithful
or free action on owners. The uniform palette bound is source-internal. -/
universe u v w z t
namespace CCO.SafeReadings
open Selectors
variable {ι : Type u} {X : ι → Type v} (S : AtomicSource.{u,v,w} ι X)
variable {Λ : Type z} [Group Λ] {N : Type t} (A : PureTagAction S Λ N)

/-- Optional converse of the actual pure tag action. -/
def centralAction (g : Λ) (rev : Bool) (D : TaggedMenu S) : TaggedMenu S :=
  if rev then Selectors.flip S (A.act g D) else A.act g D

/-- Pure action commutes with typed converse, including cross-sort names. -/
theorem centralAction_comp (g h : Λ) (r s : Bool) (D : TaggedMenu S) :
    centralAction S A g r (centralAction S A h s D) =
      centralAction S A (g*h) (Bool.xor r s) D := by
  cases r <;> cases s
  · change A.act g (A.act h D) = A.act (g*h) D
    exact (A.mul g h D).symm
  · change A.act g (Selectors.flip S (A.act h D)) = Selectors.flip S (A.act (g*h) D)
    rw [A.opposite, ← A.mul]
  · change Selectors.flip S (A.act g (A.act h D)) = Selectors.flip S (A.act (g*h) D)
    rw [← A.mul]
  · change Selectors.flip S (A.act g (Selectors.flip S (A.act h D))) = A.act (g*h) D
    rw [A.opposite, ← A.mul]
    rcases A.act (g*h) D with ⟨i,j,E⟩
    simp only [Selectors.flip, S.opposite_opposite]

theorem centralAction_two (g : Λ) (rev : Bool) (D : TaggedMenu S) :
    (centralAction S A g rev)^[2] D = A.act (g*g) D := by
  rw [Function.iterate_succ_apply', Function.iterate_one, centralAction_comp]
  simp only [Bool.xor_self, centralAction, Bool.false_eq_true, ite_false]

theorem centralAction_even_iterate (g : Λ) (rev : Bool) (n : Nat) (D : TaggedMenu S) :
    (centralAction S A g rev)^[2*n] D = A.act (g^(2*n)) D := by
  induction n generalizing D with
  | zero => simp only [Nat.mul_zero, Function.iterate_zero_apply, pow_zero, A.one]
  | succ n ih =>
    rw [show 2*(n+1) = 2*n+2 by omega, Function.iterate_add_apply,
      ih, centralAction_two, ← A.mul, ← pow_two, ← pow_add]

theorem centralAction_clears [Finite Λ] (g : Λ) (rev : Bool) (D : TaggedMenu S) :
    (centralAction S A g rev)^[2*Nat.card Λ] D = D := by
  rw [centralAction_even_iterate, Nat.mul_comm 2 (Nat.card Λ), pow_mul,
    pow_card_eq_one', one_pow, A.one]

theorem centralAction_clear_positive [Finite Λ] : 0 < 2 * Nat.card Λ := by
  have hc : 0 < Nat.card Λ := Nat.card_pos_iff.mpr ⟨inferInstance,inferInstance⟩
  omega

/-- An explicit uniform upper bound for all source loop-palette sizes. -/
noncomputable def maxLoopPalette : Nat :=
  max 1 (S.finiteSort.elems.sup fun i => Nat.card (S.Atom i i))

theorem maxLoopPalette_positive : 0 < maxLoopPalette S := by
  exact lt_of_lt_of_le (by decide : 0 < 1) (le_max_left _ _)

theorem loopPalette_card_le_max (i : ι) :
    Nat.card (S.Atom i i) ≤ maxLoopPalette S := by
  have hm : i ∈ S.finiteSort.elems := S.finiteSort.complete i
  unfold maxLoopPalette
  exact (Finset.le_sup (f := fun i => Nat.card (S.Atom i i)) hm).trans (le_max_right _ _)

end CCO.SafeReadings
