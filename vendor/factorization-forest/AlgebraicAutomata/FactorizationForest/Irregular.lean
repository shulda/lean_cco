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

public import AlgebraicAutomata.FactorizationForest.Combine

/-!
# Simon's Split Theorem — Irregular `D`-Class Case

Constructs the Simon split (`ramsey_split_irregular_case`) for the case where the `D`-class
is irregular, using the fact that the sequence length is at most 2.

## References

* [T. Colcombet, *The Factorization Forest Theorem*][colcombet2008]
-/

@[expose] public section


namespace RamseySplit

open GreensRelations

section LabelingProperties

variable {S : Type*} [Semigroup S]

/-- If an irregular `D`-class contains elements from a multiplicative sequence,
it cannot contain three consecutive products in that sequence. -/
lemma irregular_d_class_no_three_seq [Finite S] (a : S) {α : Type*} [LinearOrder α]
    (σ : MultiplicativeLabeling S α) (x y z : α) (h_img : labelingIn σ (jUp a))
    (h_xy : x < y) (h_yz : y < z) (h_d1 : IsGreenD (σ.σ x y) a) (h_d2 : IsGreenD (σ.σ y z) a) :
    IsRegularDClass (IsGreenD.eqvClass a) :=
  have h_xz_le_a : GreenJClass.mk (σ.σ x z) ≤ GreenJClass.mk a :=
    GreenJClass.mk_eq_mk_iff.mpr (isGreenJ_of_isGreenD h_d1) ▸
      σ.prop x y z h_xy h_yz ▸ IsGreenJRel.mul_right (σ.σ y z) rfl
  have h_D : IsGreenD (σ.σ x y * σ.σ y z) a := (σ.prop x y z h_xy h_yz).symm ▸
    isGreenD_of_isGreenJ
      (GreenJClass.mk_eq_mk_iff.mp (le_antisymm h_xz_le_a (h_img x z (h_xy.trans h_yz))))
  let ⟨e, he_D, he_idem, _⟩ := (mul_mem_isGreenD_eqvClass_properties ⟨a, rfl⟩ _ _ h_d1 h_d2 h_D).2
  (isRegularDClass_iff_exists_idempotent _ ⟨a, rfl⟩).mpr ⟨e, he_D, he_idem⟩

end LabelingProperties

section SplitConstruction

variable {S α : Type*} [LinearOrder α] [Semigroup S] [Fintype S]

/-- A specialized version of `combineSplits` for irregular `D`-classes.
All sequence-point elements receive the maximum rank `nSElement a - 1`,
preventing overlap with the interval ranks. -/
noncomputable abbrev irregularSplits
    (a : S) (xs : List α)
    (sY : ∀ (i : ℕ) [Nonempty (OpenIntervalType xs i)],
      Split (OpenIntervalType xs i) (nSElement a)) :
    Split α (nSElement a) :=
  combineSplits a xs
    (fun _ => ⟨nSElement a - 1, Nat.sub_lt (nSElement_pos a) Nat.zero_lt_one⟩) sY

/-- Proves the normalization and Ramsey properties for `irregularSplits`.
This is the main interface lemma for the irregular `D`-class case, delegating
to `combineSplits_props`. -/
lemma irregularSplits_props [Fintype α] [Nonempty α]
    (a : S) (xs : List α)
    (σ : MultiplicativeLabeling S α)
    (σ_Y : ∀ (i : ℕ), MultiplicativeLabeling S (OpenIntervalType xs i))
    (sY : ∀ (i : ℕ) [Nonempty (OpenIntervalType xs i)],
      Split (OpenIntervalType xs i) (nSElement a))
    (hsY_ramsey : ∀ (i : ℕ) [Nonempty (OpenIntervalType xs i)],
      IsRamsey (σ_Y i) (sY i))
    (h_min_head : xs.head? = some (Finset.min' (Finset.univ : Finset α)
      Finset.univ_nonempty))
    (h_max_val : (Finset.max' (Finset.univ : Finset (Fin (nSElement a)))
      Finset.univ_nonempty).val = nSElement a - 1)
    (h_σ_Y : ∀ i x y, (σ_Y i).σ x y = σ.σ x.val y.val)
    (h_cov : ∀ x, x ∉ xs → ∃ (i : ℕ) (hi_lt : i < xs.length),
      xs[i] < x ∧
      ∀ (h_next_lt : i + 1 < xs.length), x < xs[i + 1])
    (hsY_strict : ∀ (i : ℕ) [Nonempty (OpenIntervalType xs i)],
      ∀ z : OpenIntervalType xs i, (sY i z).val < nSElement a - 1)
    (h_xs_mono : ∀ (i j : ℕ) (hi_lt : i < xs.length) (hj_lt : j < xs.length), i < j →
      xs[i] < xs[j])
    (h_xs_len : xs.length ≤ 2)
    (h_interval_ramsey : ∀ x y, x ∉ xs → x < y →
      SplitRelation (irregularSplits a xs sY) x y →
      ∃ (i : ℕ) (x_val y_val : OpenIntervalType xs i),
        x_val.val = x ∧ y_val.val = y ∧
        SplitRelation (@sY i ⟨x_val⟩) x_val y_val) :
    IsNormalized (irregularSplits a xs sY) ∧
    IsRamsey σ (irregularSplits a xs sY) := by
  have h_lt : ∀ (i j : ℕ) (hi : i < xs.length) (hj : j < xs.length), xs[i] < xs[j] → i < j := by
    intro i j hi hj h_get
    by_contra! h_le
    rcases h_le.eq_or_lt with rfl | h_lt'
    · exact lt_irrefl _ h_get
    · exact lt_asymm h_get (h_xs_mono j i hj hi h_lt')
  exact combineSplits_props a xs (nSElement a - 1) σ σ_Y
    (fun _ ↦ ⟨nSElement a - 1, Nat.sub_lt (nSElement_pos a) Nat.zero_lt_one⟩)
    sY hsY_ramsey h_σ_Y h_cov hsY_strict
    (h_rankX_ge := fun _ _ ↦ le_rfl) (h_xs_mono := h_xs_mono)
    (h_interval_ramsey := h_interval_ramsey)
    (h_X_ramsey_1 := fun x y z hx hy hz hlt_xy hlt_yz _ _ ↦ by
      rcases List.mem_iff_getElem.mp hx with ⟨ix, hix, rfl⟩
      rcases List.mem_iff_getElem.mp hy with ⟨iy, hiy, rfl⟩
      rcases List.mem_iff_getElem.mp hz with ⟨iz, hiz, rfl⟩
      have h_ix_iy := h_lt ix iy hix hiy hlt_xy
      have h_iy_iz := h_lt iy iz hiy hiz hlt_yz
      omega)
    (h_X_ramsey_2 := fun x y u v hx hy hu hv hlt_xy hlt_uv _ _ _ ↦ by
      rcases List.mem_iff_getElem.mp hx with ⟨ix, hix, rfl⟩
      rcases List.mem_iff_getElem.mp hy with ⟨iy, hiy, rfl⟩
      rcases List.mem_iff_getElem.mp hu with ⟨iu, hiu, rfl⟩
      rcases List.mem_iff_getElem.mp hv with ⟨iv, hiv, rfl⟩
      have h_ix_iy := h_lt ix iy hix hiy hlt_xy
      have h_iu_iv := h_lt iu iv hiu hiv hlt_uv
      have h1 : ix = iu := by omega
      have h2 : iy = iv := by omega
      subst h1
      subst h2
      rfl)
    (h_min_norm := by
      cases xs with
      | nil => cases h_min_head
      | cons hd tl =>
        have h_min_in : Finset.min' (Finset.univ : Finset α) Finset.univ_nonempty ∈ hd :: tl := by
          simp only [List.head?_cons, Option.some.injEq] at h_min_head
          rw [← h_min_head]
          exact .head _
        simp only [combineSplits, dite_eq_left h_min_in])
    (h_max_val := h_max_val)

/-- Constructs a normalized Ramsey split when the `D`-class of `a` is irregular. -/
lemma ramsey_split_irregular_case [Fintype α] [Nonempty α]
    (a : S)
    (σ : MultiplicativeLabeling S α) (h_img : labelingIn σ (jUp a))
    (h_not_reg : ¬ IsRegularDClass (IsGreenD.eqvClass a))
    (ih : ∀ b : S, nSElement b < nSElement a →
    ∀ (xs : List α) (i : ℕ) [Nonempty (OpenIntervalType xs i)]
    (σ_β : MultiplicativeLabeling S (OpenIntervalType xs i)), labelingIn σ_β (jUp b) →
    ∃ (s : Split (OpenIntervalType xs i) (nSElement b)), IsNormalized s ∧ IsRamsey σ_β s) :
    ∃ (s : Split α (nSElement a)), IsNormalized s ∧ IsRamsey σ s := by
  classical
  let x₀ := Finset.min' (Finset.univ : Finset α) Finset.univ_nonempty
  let xs := buildXSeq a σ x₀
  let σ_Y (i : ℕ) : MultiplicativeLabeling S (OpenIntervalType xs i) :=
    ⟨fun x y ↦ σ.σ x.val y.val, fun x y z hx hy ↦ σ.prop x.val y.val z.val hx hy⟩
  have h_sY_ex : ∀ i [Nonempty (OpenIntervalType xs i)],
      ∃ (s : Split (OpenIntervalType xs i) (nSElement a)),
        IsRamsey (σ_Y i) s ∧ ∀ z, (s z).val < nSElement a - nD (IsGreenD.eqvClass a) :=
    build_interval_splits_of_ih a σ h_img xs (buildXSeq_properties a σ h_img x₀).2.2.1 ih
  choose sY hsY_ramsey hsY_strict using h_sY_ex
  have hsY_strict' : ∀ (i : ℕ) [Nonempty (OpenIntervalType xs i)] (z : OpenIntervalType xs i),
      (sY i z).val < nSElement a - 1 :=
    fun i _ z ↦ (ite_eq_right h_not_reg : nD (IsGreenD.eqvClass a) = 1) ▸ hsY_strict i z
  have h_xs_len : xs.length ≤ 2 := by
    by_contra! h_len
    obtain ⟨-, h_d, -, h_mono⟩ := buildXSeq_properties a σ h_img x₀
    have h01 := h_mono 0 1 (by lia) (by lia) (by omega)
    have h12 := h_mono 1 2 (by lia) (by omega) (by omega)
    have h0_mem : xs[0] ∈ xs := xs.getElem_mem (by lia)
    have h1_mem : xs[1] ∈ xs := xs.getElem_mem (by lia)
    have h2_mem : xs[2] ∈ xs := xs.getElem_mem (by omega)
    exact h_not_reg (irregular_d_class_no_three_seq a σ xs[0] xs[1] xs[2] h_img h01 h12
      (h_d xs[0] h0_mem xs[1] h1_mem h01)
      (h_d xs[1] h1_mem xs[2] h2_mem h12))
  exact ⟨irregularSplits a xs sY, irregularSplits_props a xs σ σ_Y sY hsY_ramsey
    (h_xs_mono := (buildXSeq_properties a σ h_img x₀).2.2.2) (h_xs_len := h_xs_len)
    (h_min_head := by
      dsimp [xs]
      rw [buildXSeq]
      split_ifs <;> rfl)
    (h_max_val := by
      have : Nonempty (Fin (nSElement a)) := Fin.pos_iff_nonempty.mp (nSElement_pos a)
      rw [Fin.val_max'_univ])
    (h_σ_Y := fun _ _ _ ↦ rfl)
    (h_cov := fun x hx ↦ buildXSeq_covers a σ x₀ x (Finset.min'_le _ _ (Finset.mem_univ x)) hx)
    (hsY_strict := hsY_strict')
    (h_interval_ramsey := combineSplits_interval_ramsey a xs
      (fun _ ↦ ⟨nSElement a - 1, Nat.sub_lt (nSElement_pos a) Nat.zero_lt_one⟩)
      sY (nSElement a - 1) (buildXSeq_properties a σ h_img x₀).2.2.2
      (fun x hx ↦ buildXSeq_covers a σ x₀ x (Finset.min'_le _ _ (Finset.mem_univ x)) hx)
      hsY_strict' (fun _ ↦ le_rfl))⟩

end SplitConstruction

end RamseySplit
