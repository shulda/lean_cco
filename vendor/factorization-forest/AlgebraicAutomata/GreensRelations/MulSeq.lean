/-
Copyright (c) 2026 Re'em Melamed-Katz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Re'em Melamed-Katz
-/

/- CCO compatibility port, 6 November 2026.
Adapted from ReemMelamed/algebraic-automata at
0acb244aaa913c32eeeff48e939cb5df469a3f70 for the receiving
Lean 4.34.1 / Mathlib v4.34.1 environment. Original notices retained.
Compatibility modifications are recorded in PROVENANCE.json and PORT_REPORT.md. -/

module

public import AlgebraicAutomata.GreensRelations.Basic
public import Mathlib.Basic.Finite.Defs
public import AlgebraicAutomata.ForMathlib.Algebra.Group.Opposite
public import Mathlib.Data.Fintype.Pigeonhole

/-!
# Multiplication Sequences and Helper Lemmas

Tools for analyzing finite semigroups via iterated multiplication sequences (`leftMulSeq`,
`rightMulSeq`) and pigeonhole arguments.

## References

* [T. Colcombet, *The Factorization Forest Theorem*][colcombet2008]
-/

@[expose] public section


namespace GreensRelations

open MulOpposite

variable {S : Type*} [Semigroup S]

namespace MulSeq

/-- The sequence defined by repeatedly multiplying `a` by `c` on the right. -/
def rightMulSeq (a c : S) (n : ℕ) : S := (· * c)^[n] a

@[simp] lemma rightMulSeq_zero (a c : S) : rightMulSeq a c 0 = a := rfl

@[simp] lemma rightMulSeq_succ (a c : S) (n : ℕ) :
    rightMulSeq a c (n + 1) = rightMulSeq a c n * c :=
  Function.iterate_succ_apply' (· * c) n a

/-- Left multiplication can be pulled out of a `rightMulSeq`. -/
lemma rightMulSeq_mul_pull (c : S) (m : ℕ) (x u : S) :
    rightMulSeq (u * x) c m = u * rightMulSeq x c m := by
  induction m with
  | zero => rfl
  | succ m ih =>
    simp only [rightMulSeq_succ, ih, mul_assoc]

/-- The sequence defined by repeatedly multiplying `a` by `c` on the left. -/
def leftMulSeq (c a : S) (n : ℕ) : S := (c * ·)^[n] a

@[simp] lemma leftMulSeq_zero (c a : S) : leftMulSeq c a 0 = a := rfl

@[simp] lemma leftMulSeq_succ (c a : S) (n : ℕ) :
    leftMulSeq c a (n + 1) = c * leftMulSeq c a n :=
  Function.iterate_succ_apply' (c * ·) n a

/-- Extracting a left multiplication from the base of a `leftMulSeq`. -/
lemma leftMulSeq_pull_c (c : S) (n : ℕ) (x : S) :
    leftMulSeq c x (n + 1) = leftMulSeq c (c * x) n :=
  Function.iterate_succ_apply (c * ·) n x

/-- In a finite semigroup, a `leftMulSeq` eventually repeats. -/
lemma leftMulSeq_pigeonhole [Finite S] (c a : S) :
    ∃ i j : ℕ, i < j ∧ leftMulSeq c a i = leftMulSeq c a j :=
  let ⟨i, j, hne, heq⟩ := Finite.exists_ne_map_eq_of_infinite (leftMulSeq c a)
  hne.lt_or_gt.elim (⟨i, j, ·, heq⟩) (⟨j, i, ·, heq.symm⟩)

/-- Any element in a `leftMulSeq` starting from `a` is a left multiple of `a`. -/
lemma leftMulSeq_isGreenLeftDvd (c a : S) : (m : ℕ) → IsGreenLeftDvd (leftMulSeq c a m) a
  | 0 => .inl rfl
  | m + 1 =>
    IsGreenLeftDvd.trans (.inr ⟨c, leftMulSeq_succ c a m⟩) (leftMulSeq_isGreenLeftDvd c a m)

/-- Left and right multiplication sequences commute. -/
lemma leftMulSeq_rightMulSeq_comm (c x d : S) (i k : ℕ) :
    leftMulSeq c (rightMulSeq x d k) i = rightMulSeq (leftMulSeq c x i) d k := by
  induction i with
  | zero => rfl
  | succ i ih =>
    simp only [leftMulSeq_succ, ih, ← rightMulSeq_mul_pull]

/-- If `b = c * b * d`, applying `n` left steps then `n` right steps yields `b`. -/
lemma b_eq_right_left_seq (c b d : S) (h : b = c * b * d) (n : ℕ) :
    b = rightMulSeq (leftMulSeq c b n) d n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    grind only [rightMulSeq_mul_pull, leftMulSeq_succ, rightMulSeq_succ]

/-- Alias for `b_eq_right_left_seq` following Mathlib naming convention. -/
abbrev mul_rightMulSeq_leftMulSeq_eq := @b_eq_right_left_seq

/-- Left multiplication sequence addition of indices. -/
lemma leftMulSeq_add (c a : S) (n m : ℕ) :
    leftMulSeq c a (n + m) = leftMulSeq c (leftMulSeq c a n) m :=
  (congrArg (fun k ↦ (c * ·)^[k] a) (Nat.add_comm n m)).trans
    (Function.iterate_add_apply (c * ·) m n a)

/-- If `b = c * b * d` in a finite semigroup, `b` is equivalent to some left multiple sequence. -/
lemma eq_leftMulSeq_of_eq_mul_mul [Finite S] {b c d : S} (h : b = c * b * d) :
    ∃ k, 0 < k ∧ b = leftMulSeq c b k := by
  rcases leftMulSeq_pigeonhole c b with ⟨i, j, hij, heq⟩
  have h_fi_k : leftMulSeq c (leftMulSeq c b i) (j - i) = leftMulSeq c b i := by
    rw [← leftMulSeq_add, Nat.add_sub_of_le (le_of_lt hij), heq]
  have h_b_eq := b_eq_right_left_seq c b d h i
  exact ⟨j - i, Nat.sub_pos_of_lt hij, by
    conv_lhs => rw [h_b_eq]
    rw [← h_fi_k, ← leftMulSeq_rightMulSeq_comm, ← h_b_eq]⟩

/-- If `b = c * b * d`, then `b` is `L`-related to `c * b`. -/
lemma greenL_of_eq_mul_mul [Finite S] {b c d : S} (h : b = c * b * d) : IsGreenL b (c * b) := by
  obtain ⟨k, hk_pos, hk_eq⟩ := eq_leftMulSeq_of_eq_mul_mul h
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk_pos.ne'
  have h1 : IsGreenLeftDvd b (c * b) := by
    conv_lhs => rw [hk_eq, leftMulSeq_pull_c]
    exact leftMulSeq_isGreenLeftDvd c (c * b) m
  exact ⟨h1, Or.inr ⟨c, rfl⟩⟩

/-- If `b = c * b * d`, then `b` is `R`-related to `b * d`. -/
lemma greenR_of_eq_mul_mul [Finite S] {b c d : S} (h : b = c * b * d) : IsGreenR b (b * d) := by
  rw [isGreenR_iff_isGreenL_op]
  grind only [op_mul, mul_assoc, isGreenR_iff_isGreenL_op, greenL_of_eq_mul_mul]

/-- Green's `L`-relation holds when a left multiplier is dropped from an
already `L`-related element. -/
lemma isGreenL_of_isGreenL_mul {b x z : S} (h : IsGreenL b (x * (z * b))) : IsGreenL b (z * b) :=
  ⟨IsGreenLeftDvd.trans h.left (Or.inr ⟨x, rfl⟩), Or.inr ⟨z, rfl⟩⟩

/-- If `a` is a left multiple of `b` and `b` is a two-sided multiple of `a` in a finite semigroup,
  then `a` and `b` are `L`-related. -/
lemma isGreenL_of_isGreenLeftDvd_of_isGreenJRel [Finite S] {a b : S}
    (hL : IsGreenLeftDvd a b) (hJ : IsGreenJRel b a) : IsGreenL a b := by
  rcases hL with rfl | ⟨c, rfl⟩
  · exact IsGreenL.refl a
  · rcases IsGreenJRel.iff_exists_left_right.mp hJ with ⟨z, hzL, hzR⟩
    have h_cb : IsGreenL b (c * b) := by
      rcases hzL with rfl | ⟨u, rfl⟩
      · rcases hzR with h | ⟨v, h⟩
        · exact h ▸ IsGreenL.refl b
        · exact greenL_of_eq_mul_mul h
      · rcases hzR with h | ⟨v, h⟩
        · exact ⟨.inr ⟨u, congrArg (u * ·) h⟩, .inr ⟨c, rfl⟩⟩
        · have h_eq : u * z = (u * c) * (u * z) * v :=
            (congrArg (u * ·) h).trans (by simp only [mul_assoc])
          have h1 := greenL_of_eq_mul_mul h_eq
          rw [mul_assoc] at h1
          exact isGreenL_of_isGreenL_mul h1
    exact h_cb.symm

/-- If `a` is a right multiple of `b` and `b` is a two-sided multiple of `a` in a finite semigroup,
  then `a` and `b` are `R`-related. -/
lemma isGreenR_of_isGreenRightDvd_of_isGreenJRel [Finite S] {a b : S}
    (hR : IsGreenRightDvd a b) (hJ : IsGreenJRel b a) : IsGreenR a b :=
  isGreenR_iff_isGreenL_op.mpr
    (isGreenL_of_isGreenLeftDvd_of_isGreenJRel
      (isGreenRightDvd_iff_isGreenLeftDvd_op.mp hR) hJ.op)

/-- A regular element `a` has an idempotent in its `L`-class. -/
lemma exists_idempotent_in_greenL_of_regular {a : S}
    (hReg : IsGreenRegular a) : ∃ e ∈ IsGreenL.eqvClass a, IsIdempotentElem e :=
  let ⟨s, hs⟩ := hReg
  ⟨s * a, ⟨Or.inr ⟨s, rfl⟩, Or.inr ⟨a, by rw [← mul_assoc, hs]⟩⟩,
    show s * a * (s * a) = s * a by rw [mul_assoc, ← mul_assoc a, hs]⟩

/-- A regular element `a` has an idempotent in its `R`-class. -/
lemma exists_idempotent_in_greenR_of_regular {a : S}
    (hReg : IsGreenRegular a) : ∃ e ∈ IsGreenR.eqvClass a, IsIdempotentElem e :=
  let ⟨s, hs⟩ := hReg
  ⟨a * s, ⟨Or.inr ⟨s, rfl⟩, Or.inr ⟨a, hs.symm⟩⟩,
    show a * s * (a * s) = a * s by rw [← mul_assoc, hs]⟩

/-- If `a` is `H`-related to an idempotent `e`,
  multiplying `a` by `e` leaves `a` unchanged. -/
lemma mul_eq_self_of_isGreenH_idempotent {a e : S}
    (h : IsGreenH a e) (he : IsIdempotentElem e) : a * e = a ∧ e * a = a :=
  ⟨by rcases h.left.left with rfl | ⟨w, rfl⟩ <;> simp only [mul_assoc, he.eq],
   by rcases h.right.left with rfl | ⟨v, rfl⟩ <;> simp only [← mul_assoc, he.eq]⟩

/-- Two `H`-related idempotents must be equal. -/
lemma eq_of_isGreenH_of_idempotent {a b : S}
    (h : IsGreenH a b) (ha : IsIdempotentElem a) (hb : IsIdempotentElem b) : a = b :=
  ((mul_eq_self_of_isGreenH_idempotent h hb).1).symm.trans
    ((mul_eq_self_of_isGreenH_idempotent h.symm ha).2)

end MulSeq

end GreensRelations
