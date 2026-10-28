import CCO.ParityHasse.Sparse.Deletion
import CCO.ParityHasse.Sparse.Statements

/-! Translate actual edge-set deletion into the finite graph statement, and
retain every robust edge set after a bounded number of actual deletions. -/

namespace CCO.ParityHasse.Sparse

noncomputable section

universe u
variable {V : Type u} [DecidableEq V]

/-- The simple graph of an actual unordered edge set; diagonals are excluded. -/
def simpleGraphOfEdges (E : Finset (Sym2 V)) : SimpleGraph V where
  Adj x y := x ≠ y ∧ s(x, y) ∈ E
  symm := ⟨by
    intro x y h
    exact ⟨h.1.symm, by simpa only [Sym2.eq_swap] using h.2⟩⟩
  loopless := ⟨by intro x h; exact h.1 rfl⟩

@[simp] theorem simpleGraphOfEdges_adj (E : Finset (Sym2 V)) (x y : V) :
    (simpleGraphOfEdges E).Adj x y ↔ x ≠ y ∧ s(x, y) ∈ E := Iff.rfl

/-- The literal finite ordinal associated with a modular cyclic position. -/
def zmodFinCode (ℓ : ℕ) [NeZero ℓ] : ZMod ℓ ↪ Fin ℓ where
  toFun j := ⟨j.val, j.val_lt⟩
  inj' := by intro j k h; exact (ZMod.val_injective ℓ) (congrArg Fin.val h)

@[simp] theorem zmodFinCode_val (ℓ : ℕ) [NeZero ℓ] (j : ZMod ℓ) :
    (zmodFinCode ℓ j).val = j.val := rfl

lemma zmodFinCode_add_one {ℓ : ℕ} (hℓ : 3 ≤ ℓ) [NeZero ℓ] (j : ZMod ℓ) :
    zmodFinCode ℓ (j + 1) = CCO.cyclicNext (by omega) (zmodFinCode ℓ j) := by
  apply Fin.ext
  change (j + 1).val = (j.val + 1) % ℓ
  have h1 : (1 : ZMod ℓ).val = 1 := by
    simpa only [Nat.cast_one] using ZMod.val_natCast_of_lt (n := ℓ) (a := 1) (by omega : 1 < ℓ)
  rw [ZMod.val_add, h1]

/-- Literal ZMod cycle-freeness implies the exact Fin-cycle predicate used by CCO. -/
theorem noShortCycles_of_shortCycleFree [Fintype V] {g : ℕ} {E : Finset (Sym2 V)}
    (hfree : ShortCycleFree g E) : NoShortCycles (simpleGraphOfEdges E) g := by
  intro ℓ hℓ hlg f hcycle
  letI : NeZero ℓ := ⟨by omega⟩
  let code : CycleCode V ℓ := (zmodFinCode ℓ).trans f
  have hsub : cyclicEdges code ⊆ E := by
    intro e he
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp he
    have hj := hcycle (zmodFinCode ℓ j)
    rw [← zmodFinCode_add_one hℓ j] at hj
    exact hj.2
  let L : ShortLength g := ⟨⟨ℓ, by omega⟩, hℓ⟩
  have hcodes : supportedCodes (ℓ := ℓ) E = ∅ := hfree L
  have hm : code ∈ supportedCodes E := (mem_supportedCodes E code).2 hsub
  rw [hcodes] at hm
  exact Finset.notMem_empty code hm

/-- Every robust actual edge set survives the bounded deletion step. -/
theorem bounded_deletion_retains {A : Type*} [DecidableEq A]
    {E F K : Finset A} {B : ℝ} (hKE : K ⊆ E)
    (hrobust : B < (K.card : ℝ)) (hremoved : ((E \ F).card : ℝ) ≤ B) :
    ∃ e ∈ K, e ∈ F := by
  by_contra hnone
  have hsub : K ⊆ E \ F := by
    intro e he
    apply Finset.mem_sdiff.mpr
    exact ⟨hKE he, fun heF => hnone ⟨e, he, heF⟩⟩
  have hc : (K.card : ℝ) ≤ ((E \ F).card : ℝ) := by
    exact_mod_cast Finset.card_le_card hsub
  linarith

end

end CCO.ParityHasse.Sparse
