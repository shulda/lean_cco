import CCO.ParityHasse.Sparse.Cycles
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith

/-!
# Finite deletion of all short cycles

The potential is the sum of oriented injective cycle counts divided by 2ℓ.
Erasing one edge of a witnessed cycle drops its own summand by at least one;
all other summands can only decrease. The resulting finite induction counts
actual deleted edges and never invokes an abstract graph-existence premise.
-/

open scoped BigOperators

namespace CCO.ParityHasse.Sparse

noncomputable section

universe u
variable {V : Type u} [Fintype V] [DecidableEq V]

abbrev ShortLength (g : ℕ) := {ℓ : Fin (g + 1) // 3 ≤ ℓ.val}

instance shortLength_neZero {g : ℕ} (ℓ : ShortLength g) : NeZero ℓ.1.val :=
  ⟨by have h := ℓ.2; omega⟩

/-- Normalized oriented count at one literal length. -/
def cycleTerm {g : ℕ} (E : Finset (Sym2 V)) (ℓ : ShortLength g) : ℝ :=
  ((supportedCodes (ℓ := ℓ.1.val) E).card : ℝ) / (2 * ℓ.1.val)

/-- The actual number of short unoriented cycles, expressed without a quotient. -/
def cycleMass (g : ℕ) (E : Finset (Sym2 V)) : ℝ :=
  ∑ ℓ : ShortLength g, cycleTerm E ℓ

lemma cycleTerm_nonneg {g : ℕ} (E : Finset (Sym2 V)) (ℓ : ShortLength g) :
    0 ≤ cycleTerm E ℓ := by unfold cycleTerm; positivity

lemma cycleTerm_mono {g : ℕ} {E F : Finset (Sym2 V)} (hEF : E ⊆ F)
    (ℓ : ShortLength g) : cycleTerm E ℓ ≤ cycleTerm F ℓ := by
  have hc : ((supportedCodes (ℓ := ℓ.1.val) E).card : ℝ) ≤
      ((supportedCodes (ℓ := ℓ.1.val) F).card : ℝ) := by
    exact_mod_cast Finset.card_le_card (supportedCodes_mono hEF)
  exact div_le_div_of_nonneg_right hc (by positivity)

lemma cycleMass_nonneg (g : ℕ) (E : Finset (Sym2 V)) : 0 ≤ cycleMass g E :=
  Finset.sum_nonneg (fun ℓ _ => cycleTerm_nonneg E ℓ)

lemma cycleMass_mono (g : ℕ) {E F : Finset (Sym2 V)} (hEF : E ⊆ F) :
    cycleMass g E ≤ cycleMass g F :=
  Finset.sum_le_sum (fun ℓ _ => cycleTerm_mono hEF ℓ)

/-- One actual short cycle supplies a decrease by one in the total mass. -/
theorem cycleMass_erasure_drop {g : ℕ} {E : Finset (Sym2 V)}
    (ℓ₀ : ShortLength g) (f : CycleCode V ℓ₀.1.val)
    (hf : cyclicEdges f ⊆ E) {e : Sym2 V} (he : e ∈ cyclicEdges f) :
    cycleMass g (E.erase e) + 1 ≤ cycleMass g E := by
  have hs : (∑ ℓ : ShortLength g,
      (cycleTerm (E.erase e) ℓ + if ℓ = ℓ₀ then (1 : ℝ) else 0)) ≤
      ∑ ℓ : ShortLength g, cycleTerm E ℓ := by
    apply Finset.sum_le_sum
    intro ℓ hℓ
    by_cases h : ℓ = ℓ₀
    · subst ℓ
      simp only [if_pos rfl]
      exact normalized_cycle_count_erasure_drop ℓ₀.2 f hf he
    · simp only [if_neg h, add_zero]
      exact cycleTerm_mono (Finset.erase_subset e E) ℓ
  simpa only [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true,
    cycleMass] using hs

/-- No injective cyclic code of any length from 3 through g is supported. -/
def ShortCycleFree (g : ℕ) (E : Finset (Sym2 V)) : Prop :=
  ∀ ℓ : ShortLength g, (supportedCodes (ℓ := ℓ.1.val) E) = ∅

/-- Greedy edge deletion realizes the source's deterministic sparsening step. -/
theorem delete_short_cycles (g : ℕ) (E : Finset (Sym2 V)) :
    ∃ F : Finset (Sym2 V), F ⊆ E ∧ ShortCycleFree g F ∧
      ((E \ F).card : ℝ) ≤ cycleMass g E := by
  classical
  refine Finset.strongInductionOn E ?_
  intro E ih
  by_cases hfree : ShortCycleFree g E
  · exact ⟨E, Finset.Subset.refl _, hfree, by simpa using cycleMass_nonneg g E⟩
  · change ¬ ∀ ℓ : ShortLength g, supportedCodes (ℓ := ℓ.1.val) E = ∅ at hfree
    obtain ⟨ℓ, hℓ⟩ := not_forall.mp hfree
    obtain ⟨f, hf⟩ := Finset.nonempty_iff_ne_empty.mpr hℓ
    have hf' := (mem_supportedCodes E f).1 hf
    have hne : (cyclicEdges f).Nonempty := by
      apply Finset.card_pos.mp
      rw [cyclicEdges_card ℓ.2]
      have hp := ℓ.2
      omega
    obtain ⟨e, he⟩ := hne
    have heE : e ∈ E := hf' he
    obtain ⟨F, hF, hfreeF, hcountF⟩ := ih (E.erase e) (Finset.erase_ssubset heE)
    have hFE : F ⊆ E := hF.trans (Finset.erase_subset e E)
    have hcount : (E \ F).card = ((E.erase e) \ F).card + 1 := by
      rw [Finset.card_sdiff_of_subset hFE, Finset.card_sdiff_of_subset hF,
        Finset.card_erase_of_mem heE]
      have hc := Finset.card_le_card hF
      rw [Finset.card_erase_of_mem heE] at hc
      have hpos : 0 < E.card := Finset.card_pos.mpr ⟨e, heE⟩
      omega
    refine ⟨F, hFE, hfreeF, ?_⟩
    rw [hcount, Nat.cast_add, Nat.cast_one]
    linarith [cycleMass_erasure_drop ℓ f hf' he]
end

end CCO.ParityHasse.Sparse
