import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Sym.Sym2
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# Oriented injective cycle codes and their dihedral symmetries

The graph is encoded by an actual finite set of unordered pairs. Counting
oriented injective cyclic embeddings avoids constructing a quotient of cycles.
-/

namespace CCO.ParityHasse.Sparse

noncomputable section

universe u

abbrev CycleCode (V : Type u) (ℓ : ℕ) := ZMod ℓ ↪ V

variable {V : Type u} {ℓ : ℕ}

/-- Actual unoriented edges traversed by an injective cyclic code. -/
def cyclicEdges [NeZero ℓ] [DecidableEq V] (f : CycleCode V ℓ) : Finset (Sym2 V) :=
  Finset.univ.image (fun j => s(f j, f (j + 1)))

lemma zmod_two_ne_zero (hℓ : 3 ≤ ℓ) : (2 : ZMod ℓ) ≠ 0 := by
  intro h
  have hv := congrArg ZMod.val h
  simp only [ZMod.val_ofNat, ZMod.val_zero] at hv
  rw [Nat.mod_eq_of_lt (by omega : 2 < ℓ)] at hv
  omega

lemma zmod_one_ne_neg_one (hℓ : 3 ≤ ℓ) : (1 : ZMod ℓ) ≠ -1 := by
  intro h
  apply zmod_two_ne_zero hℓ
  calc
    (2 : ZMod ℓ) = 1 + 1 := by ring
    _ = -1 + 1 := congrArg (fun x : ZMod ℓ => x + 1) h
    _ = 0 := by ring

lemma edge_index_injective (hℓ : 3 ≤ ℓ) (f : CycleCode V ℓ) :
    Function.Injective (fun j => s(f j, f (j + 1))) := by
  intro j k h
  rcases Sym2.eq_iff.mp h with h | h
  · exact f.injective h.1
  · have hj : j = k + 1 := f.injective h.1
    have hk : j + 1 = k := f.injective h.2
    have htwo : (2 : ZMod ℓ) = 0 := by
      calc
        (2 : ZMod ℓ) = (j + 1) - j + ((k + 1) - k) := by ring
        _ = k - (k + 1) + ((k + 1) - k) := by rw [hk, hj]
        _ = 0 := by ring
    exact False.elim (zmod_two_ne_zero hℓ htwo)

lemma cyclicEdges_card [NeZero ℓ] [DecidableEq V] (hℓ : 3 ≤ ℓ) (f : CycleCode V ℓ) :
    (cyclicEdges f).card = ℓ := by
  rw [cyclicEdges, Finset.card_image_of_injective _ (edge_index_injective hℓ f)]
  simp [ZMod.card]

/-- Translation of a cyclic code. -/
def rotateCode (f : CycleCode V ℓ) (a : ZMod ℓ) : CycleCode V ℓ where
  toFun j := f (a + j)
  inj' := by intro j k h; exact add_left_cancel (f.injective h)

/-- Reversal with a prescribed cyclic origin. -/
def reflectCode (f : CycleCode V ℓ) (a : ZMod ℓ) : CycleCode V ℓ where
  toFun j := f (a - j)
  inj' := by
    intro j k h
    have hh : -j = -k := add_left_cancel (by simpa only [sub_eq_add_neg] using f.injective h)
    exact neg_injective hh

@[simp] lemma rotateCode_apply (f : CycleCode V ℓ) (a j : ZMod ℓ) :
    rotateCode f a j = f (a + j) := rfl

@[simp] lemma reflectCode_apply (f : CycleCode V ℓ) (a j : ZMod ℓ) :
    reflectCode f a j = f (a - j) := rfl

/-- The two orientations at each of the ℓ possible origins. -/
def dihedralCode (f : CycleCode V ℓ) (ab : ZMod ℓ × Bool) : CycleCode V ℓ :=
  if ab.2 then reflectCode f ab.1 else rotateCode f ab.1

lemma dihedralCode_injective (hℓ : 3 ≤ ℓ) (f : CycleCode V ℓ) :
    Function.Injective (dihedralCode f) := by
  rintro ⟨a, b⟩ ⟨a', b'⟩ h
  have h0 := congrArg (fun k : CycleCode V ℓ => k 0) h
  have ha : a = a' := by
    apply f.injective
    cases b <;> cases b' <;> simpa [dihedralCode] using h0
  subst a'
  have h1 := congrArg (fun k : CycleCode V ℓ => k 1) h
  cases b <;> cases b'
  · rfl
  · have hh := f.injective (show f (a + 1) = f (a - 1) by
      simpa [dihedralCode] using h1)
    have hone : (1 : ZMod ℓ) = -1 := by simpa [sub_eq_add_neg] using hh
    exact False.elim (zmod_one_ne_neg_one hℓ hone)
  · have hh := f.injective (show f (a - 1) = f (a + 1) by
      simpa [dihedralCode] using h1)
    have hone : (1 : ZMod ℓ) = -1 := by simpa [sub_eq_add_neg] using hh.symm
    exact False.elim (zmod_one_ne_neg_one hℓ hone)
  · rfl

lemma cyclicEdges_rotate [NeZero ℓ] [DecidableEq V] (f : CycleCode V ℓ) (a : ZMod ℓ) :
    cyclicEdges (rotateCode f a) = cyclicEdges f := by
  ext e
  simp only [cyclicEdges, Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨j, hj⟩
    refine ⟨a + j, ?_⟩
    simpa only [rotateCode_apply,
      show a + (j + 1) = (a + j) + 1 by ring] using hj
  · rintro ⟨j, hj⟩
    refine ⟨j - a, ?_⟩
    simpa only [rotateCode_apply,
      show a + (j - a) = j by ring,
      show a + (j - a + 1) = j + 1 by ring] using hj

lemma cyclicEdges_reflect [NeZero ℓ] [DecidableEq V] (f : CycleCode V ℓ) (a : ZMod ℓ) :
    cyclicEdges (reflectCode f a) = cyclicEdges f := by
  ext e
  simp only [cyclicEdges, Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨j, hj⟩
    refine ⟨a - (j + 1), ?_⟩
    have heq : a - (j + 1) + 1 = a - j := by ring
    simpa only [reflectCode_apply, heq,
      Sym2.eq_swap] using hj
  · rintro ⟨j, hj⟩
    refine ⟨a - j - 1, ?_⟩
    have h0 : a - (a - j - 1) = j + 1 := by ring
    have h1 : a - (a - j - 1 + 1) = j := by ring
    simpa only [reflectCode_apply, h0, h1,
      Sym2.eq_swap] using hj

lemma cyclicEdges_dihedral [NeZero ℓ] [DecidableEq V] (f : CycleCode V ℓ)
    (ab : ZMod ℓ × Bool) : cyclicEdges (dihedralCode f ab) = cyclicEdges f := by
  rcases ab with ⟨a, b⟩
  cases b
  · exact cyclicEdges_rotate f a
  · exact cyclicEdges_reflect f a


/-- All oriented injective cyclic codes whose actual edge set is present. -/
def supportedCodes [NeZero ℓ] [Fintype V] [DecidableEq V]
    (E : Finset (Sym2 V)) : Finset (CycleCode V ℓ) :=
  Finset.univ.filter (fun f => cyclicEdges f ⊆ E)

@[simp] lemma mem_supportedCodes [NeZero ℓ] [Fintype V] [DecidableEq V]
    (E : Finset (Sym2 V)) (f : CycleCode V ℓ) :
    f ∈ supportedCodes E ↔ cyclicEdges f ⊆ E := by
  simp [supportedCodes]

/-- The 2ℓ distinct codes of one unoriented cycle, without choosing a quotient. -/
def dihedralFamily [NeZero ℓ] [DecidableEq V] (f : CycleCode V ℓ) :
    Finset (CycleCode V ℓ) := Finset.univ.image (dihedralCode f)

lemma dihedralFamily_card [NeZero ℓ] [DecidableEq V] (hℓ : 3 ≤ ℓ)
    (f : CycleCode V ℓ) : (dihedralFamily f).card = 2 * ℓ := by
  rw [dihedralFamily, Finset.card_image_of_injective _ (dihedralCode_injective hℓ f)]
  simp [ZMod.card, Nat.mul_comm]

lemma supportedCodes_mono [NeZero ℓ] [Fintype V] [DecidableEq V]
    {E F : Finset (Sym2 V)} (hEF : E ⊆ F) :
    (supportedCodes E : Finset (CycleCode V ℓ)) ⊆ supportedCodes F := by
  intro f hf
  exact (mem_supportedCodes F f).2 (((mem_supportedCodes E f).1 hf).trans hEF)

/-- Erasing one edge destroys all 2ℓ distinct codes of any witnessed cycle. -/
lemma dihedralFamily_subset_erasure_loss [NeZero ℓ] [Fintype V] [DecidableEq V]
    {E : Finset (Sym2 V)} (f : CycleCode V ℓ) (hf : cyclicEdges f ⊆ E)
    {e : Sym2 V} (he : e ∈ cyclicEdges f) :
    dihedralFamily f ⊆ supportedCodes E \ supportedCodes (E.erase e) := by
  intro f' hf'
  obtain ⟨ab, _, rfl⟩ := Finset.mem_image.mp hf'
  apply Finset.mem_sdiff.mpr
  constructor
  · apply (mem_supportedCodes E _).2
    simpa only [cyclicEdges_dihedral] using hf
  · intro hnew
    have hsub := (mem_supportedCodes (E.erase e) _).1 hnew
    have he' : e ∈ cyclicEdges (dihedralCode f ab) := by
      simpa only [cyclicEdges_dihedral] using he
    have hbad := hsub he'
    exact (Finset.notMem_erase e E) hbad

/-- The exact 2ℓ decrement required for normalized oriented-cycle counting. -/
theorem supportedCodes_erasure_drop [NeZero ℓ] [Fintype V] [DecidableEq V]
    (hℓ : 3 ≤ ℓ) {E : Finset (Sym2 V)} (f : CycleCode V ℓ)
    (hf : cyclicEdges f ⊆ E) {e : Sym2 V} (he : e ∈ cyclicEdges f) :
    (supportedCodes (E.erase e) : Finset (CycleCode V ℓ)).card + 2 * ℓ ≤
      (supportedCodes E : Finset (CycleCode V ℓ)).card := by
  have hmono := supportedCodes_mono (ℓ := ℓ) (Finset.erase_subset e E)
  have hsum := Finset.card_sdiff_add_card_eq_card hmono
  have hcard := Finset.card_le_card (dihedralFamily_subset_erasure_loss f hf he)
  rw [dihedralFamily_card hℓ] at hcard
  omega

/-- Each actual edge deletion lowers normalized cycle count by at least one. -/
theorem normalized_cycle_count_erasure_drop [NeZero ℓ] [Fintype V] [DecidableEq V]
    (hℓ : 3 ≤ ℓ) {E : Finset (Sym2 V)} (f : CycleCode V ℓ)
    (hf : cyclicEdges f ⊆ E) {e : Sym2 V} (he : e ∈ cyclicEdges f) :
    ((supportedCodes (E.erase e) : Finset (CycleCode V ℓ)).card : ℝ) / (2 * ℓ) + 1 ≤
      ((supportedCodes E : Finset (CycleCode V ℓ)).card : ℝ) / (2 * ℓ) := by
  have hnat := supportedCodes_erasure_drop hℓ f hf he
  have hden : (0 : ℝ) < 2 * ℓ := by
    have : (0 : ℝ) < ℓ := by exact_mod_cast (show 0 < ℓ by omega)
    positivity
  apply (le_div_iff₀ hden).2
  rw [add_mul, div_mul_cancel₀ _ hden.ne', one_mul]
  exact_mod_cast hnat

end

end CCO.ParityHasse.Sparse
