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

public import AlgebraicAutomata.FactorizationForest.Regular
public import AlgebraicAutomata.FactorizationForest.Irregular

/-!
# Simon's Split Theorem

Assembles the regular and irregular cases to prove Simon's Split Theorem (`simon_split`),
and applies it to word labelings (`simon_word`).

## References

* [T. Colcombet, *The Factorization Forest Theorem*][colcombet2008]
-/

@[expose] public section


namespace RamseySplit

open GreensRelations

section SplitTheorem

variable {S : Type*} [Semigroup S] [Fintype S]

open Classical in
/-- Induction step for Simon's split theorem,
branching on whether the `D`-class of `a` is regular. -/
lemma simon_split_induction_aux {S : Type*} [Semigroup S] [Fintype S]
    (n : ℕ) :
    ∀ (a : S), nSElement a ≤ n →
    ∀ {α : Type*} [LinearOrder α] [Fintype α] [Nonempty α]
    (σ : MultiplicativeLabeling S α),
    labelingIn σ (jUp a) →
    ∃ (s : Split α (nSElement a)), IsNormalized s ∧ IsRamsey σ s :=
  Nat.strong_induction_on n fun _ ihn a hna {α} _ _ _ σ h_img ↦
    have ih : ∀ b : S, nSElement b < nSElement a →
        ∀ (xs : List α) (i : ℕ) [Nonempty (OpenIntervalType xs i)]
        (σ_β : MultiplicativeLabeling S (OpenIntervalType xs i)), labelingIn σ_β (jUp b) →
        ∃ (s : Split (OpenIntervalType xs i) (nSElement b)), IsNormalized s ∧ IsRamsey σ_β s :=
      fun b hb _xs _i _ σ_β h_img_β ↦ ihn (nSElement b) (hb.trans_le hna) b le_rfl σ_β h_img_β
    if h_reg : IsRegularDClass (IsGreenD.eqvClass a) then
      ramsey_split_regular_case a σ h_img h_reg ih
    else
      ramsey_split_irregular_case a σ h_img h_reg ih

/-- Simon's Theorem (Split Form): every multiplicative labeling admits a normalized Ramsey split. -/
theorem simon_split {S α : Type*} [Semigroup S] [Fintype S]
    [LinearOrder α] [Fintype α] [Nonempty α] [Nonempty (Fin (nS S))]
    (σ : MultiplicativeLabeling S α) :
    ∃ (s : Split α (nS S)), IsNormalized s ∧ IsRamsey σ s := by
  let x₀ := Finset.min' (Finset.univ : Finset α) Finset.univ_nonempty
  let y₀ := Finset.max' (Finset.univ : Finset α) Finset.univ_nonempty
  let a := σ.σ x₀ y₀
  have ha : labelingIn σ (jUp a) := fun x y hlt ↦
    labeling_factor_le_J σ x₀ x y y₀
      (Finset.min'_le _ _ (Finset.mem_univ _)) hlt (Finset.le_max' _ _ (Finset.mem_univ _))
  obtain ⟨s_a, h_norm, h_ramsey⟩ := simon_split_induction_aux (nSElement a) a le_rfl σ ha
  have h_le : nSElement a ≤ nS S := by
    dsimp [nS]
    have h_ne : (Finset.univ.image (fun (x : S) ↦ nSElement x)).Nonempty :=
      ⟨nSElement a, Finset.mem_image_of_mem _ (Finset.mem_univ a)⟩
    rw [dite_eq_left h_ne]
    exact Finset.le_max' _ _ (Finset.mem_image_of_mem _ (Finset.mem_univ a))
  let Δ := nS S - nSElement a
  let f : Fin (nSElement a) → Fin (nS S) := fun x ↦ ⟨x.val + Δ, by
    have h_sa_lt := x.isLt
    omega⟩
  have hf : StrictMono f := fun x y hij ↦
    Fin.lt_def.2 (by
      dsimp [f]
      have hlt := Fin.lt_def.1 hij
      omega)
  let s : Split α (nS S) := f ∘ s_a
  exact ⟨s, by
      ext
      simp only [s, Function.comp_apply, h_norm]
      dsimp [f]
      have : Nonempty (Fin (nSElement a)) := Fin.pos_iff_nonempty.mp (nSElement_pos a)
      have : Nonempty (Fin (nS S)) := ‹_›
      rw [Fin.val_max'_univ, Fin.val_max'_univ]
      omega,
    h_ramsey.comp_strictMono f hf⟩

end SplitTheorem

section SimonWord

/-- Simon's split theorem for words: every word admits a normalized Ramsey split of size `nS S`. -/
theorem simon_word {A S : Type*} [Semigroup S] [Fintype S]
    [Nonempty (Fin (nS S))]
    (eval : List A → S)
    (hmul : ∀ u v, u ≠ [] → v ≠ [] → eval (u ++ v) = eval u * eval v)
    (u : List A) :
    ∃ s : Split (Fin (u.length + 1)) (nS S),
      IsNormalized s ∧ IsRamsey (wordLabeling eval hmul u) s :=
  simon_split (wordLabeling eval hmul u)

end SimonWord

end RamseySplit
