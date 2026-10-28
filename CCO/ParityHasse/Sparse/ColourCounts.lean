import CCO.ParityHasse.Sparse.Bounds
import Mathlib.Data.Sym.Card
import Mathlib.Data.Finset.Prod

/-!
# Actual monochromatic unordered pair counts

A monochromatic pair is an actual unordered pair of DISTINCT vertices.
The finite colour classes may be empty.
-/

open scoped BigOperators

namespace CCO.ParityHasse.Sparse

universe u

variable {V : Type u} [Fintype V] [DecidableEq V] {q : ℕ}

def colourClass (κ : V → Fin q) (d : Fin q) : Finset V :=
  Finset.univ.filter (fun v => κ v = d)

@[simp] lemma mem_colourClass (κ : V → Fin q) (d : Fin q) (v : V) :
    v ∈ colourClass κ d ↔ κ v = d := by simp [colourClass]

/-- The actual non-diagonal edges lying in one colour class. -/
def monochromaticClassPairs (κ : V → Fin q) (d : Fin q) : Finset (Sym2 V) :=
  (colourClass κ d).offDiag.image Sym2.mk.uncurry

/-- All actual monochromatic unordered pairs, over all colour classes. -/
def classPairUnion (κ : V → Fin q) : Finset (Sym2 V) :=
  Finset.univ.biUnion (monochromaticClassPairs κ)

lemma colour_class_card_sum (κ : V → Fin q) :
    ∑ d, (colourClass κ d).card = Fintype.card V := by
  have h := Finset.card_eq_sum_card_fiberwise (s := (Finset.univ : Finset V))
    (t := (Finset.univ : Finset (Fin q))) (f := κ) (by intro a ha; exact Finset.mem_univ _)
  simpa only [Finset.card_univ, colourClass] using h.symm

lemma class_pair_card_identity (κ : V → Fin q) (d : Fin q) :
    2 * (monochromaticClassPairs κ d).card + (colourClass κ d).card =
      (colourClass κ d).card ^ 2 := by
  have h := Sym2.two_mul_card_image_offDiag (colourClass κ d)
  rw [Finset.offDiag_card] at h
  have hle : (colourClass κ d).card ≤ (colourClass κ d).card * (colourClass κ d).card := by
    by_cases hz : (colourClass κ d).card = 0
    · simp [hz]
    · have hp : 1 ≤ (colourClass κ d).card := by omega
      nlinarith
  change 2 * ((colourClass κ d).offDiag.image Sym2.mk.uncurry).card + _ = _
  rw [h, Nat.sub_add_cancel hle, pow_two]

lemma class_pairs_pairwise_disjoint (κ : V → Fin q) :
    ((Finset.univ : Finset (Fin q)) : Set (Fin q)).PairwiseDisjoint (monochromaticClassPairs κ) := by
  intro d _ d' _ hdd'
  apply Finset.disjoint_left.mpr
  intro e he he'
  obtain ⟨p, hp, hpe⟩ := Finset.mem_image.mp he
  obtain ⟨p', hp', hp'e⟩ := Finset.mem_image.mp he'
  rcases Finset.mem_offDiag.mp hp with ⟨hp1, hp2, _⟩
  rcases Finset.mem_offDiag.mp hp' with ⟨hp'1, hp'2, _⟩
  have hκ1 := (mem_colourClass κ d p.1).1 hp1
  have hκ'1 := (mem_colourClass κ d' p'.1).1 hp'1
  have hκ'2 := (mem_colourClass κ d' p'.2).1 hp'2
  have hs : s(p.1, p.2) = s(p'.1, p'.2) := hpe.trans hp'e.symm
  rcases Sym2.eq_iff.mp hs with hs | hs
  · exact hdd' (hκ1.symm.trans ((congrArg κ hs.1).trans hκ'1))
  · exact hdd' (hκ1.symm.trans ((congrArg κ hs.1).trans hκ'2))

lemma classPairUnion_card (κ : V → Fin q) :
    (classPairUnion κ).card = ∑ d, (monochromaticClassPairs κ d).card := by
  exact Finset.card_biUnion (class_pairs_pairwise_disjoint κ)

/-- The exact finite counting identity preceding Cauchy--Schwarz. -/
theorem classPairUnion_count_identity (κ : V → Fin q) :
    2 * (classPairUnion κ).card + Fintype.card V =
      ∑ d, (colourClass κ d).card ^ 2 := by
  rw [classPairUnion_card, ← colour_class_card_sum κ]
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun d hd => class_pair_card_identity κ d)

/-- Every code in this finset is exactly an actual distinct same-colour pair. -/
theorem mem_classPairUnion (κ : V → Fin q) (e : Sym2 V) :
    e ∈ classPairUnion κ ↔
      ∃ x y : V, x ≠ y ∧ κ x = κ y ∧ s(x, y) = e := by
  constructor
  · intro he
    obtain ⟨d, _, he⟩ := Finset.mem_biUnion.mp he
    obtain ⟨p, hp, hpe⟩ := Finset.mem_image.mp he
    obtain ⟨hp1, hp2, hpne⟩ := Finset.mem_offDiag.mp hp
    refine ⟨p.1, p.2, hpne, ?_, hpe⟩
    exact ((mem_colourClass κ d p.1).1 hp1).trans ((mem_colourClass κ d p.2).1 hp2).symm
  · rintro ⟨x, y, hne, hκ, he⟩
    apply Finset.mem_biUnion.mpr
    refine ⟨κ x, Finset.mem_univ _, ?_⟩
    apply Finset.mem_image.mpr
    refine ⟨(x, y), ?_, he⟩
    apply Finset.mem_offDiag.mpr
    exact ⟨(mem_colourClass κ _ x).2 rfl, (mem_colourClass κ _ y).2 hκ.symm, hne⟩

/-- C01 for the actual finite colouring, including empty colour classes. -/
theorem classPairUnion_lower_bound (κ : V → Fin q) (hq : 0 < q)
    (hn : 2 * q ≤ Fintype.card V) :
    (Fintype.card V : ℝ) ^ 2 / (4 * (q : ℝ)) ≤ ((classPairUnion κ).card : ℝ) := by
  have hsum : ∑ d, ((colourClass κ d).card : ℝ) = (Fintype.card V : ℝ) := by
    exact_mod_cast colour_class_card_sum κ
  have hb := monochromatic_pair_lower_bound q hq
    (fun d => ((colourClass κ d).card : ℝ)) (Fintype.card V : ℝ) hsum (by exact_mod_cast hn)
  have hi : 2 * ((classPairUnion κ).card : ℝ) + (Fintype.card V : ℝ) =
      ∑ d, ((colourClass κ d).card : ℝ) ^ 2 := by
    exact_mod_cast classPairUnion_count_identity κ
  linarith


/-- Filter presentation used by the independent random-edge labelling. -/
def monochromaticPairs (κ : V → Fin q) : Finset (Sym2 V) :=
  Finset.univ.filter (fun e => ¬ e.IsDiag ∧ (e.map κ).IsDiag)

theorem mem_monochromaticPairs (κ : V → Fin q) (e : Sym2 V) :
    e ∈ monochromaticPairs κ ↔
      ∃ x y : V, x ≠ y ∧ κ x = κ y ∧ s(x, y) = e := by
  refine Sym2.inductionOn e ?_
  intro x y
  simp only [monochromaticPairs, Finset.mem_filter, Finset.mem_univ, true_and,
    Sym2.map_mk, Sym2.mk_isDiag_iff]
  constructor
  · rintro ⟨hne, hκ⟩
    exact ⟨x, y, hne, hκ, rfl⟩
  · rintro ⟨a, b, hne, hκ, hab⟩
    rcases Sym2.eq_iff.mp hab with h | h
    · rcases h with ⟨rfl, rfl⟩
      exact ⟨hne, hκ⟩
    · rcases h with ⟨rfl, rfl⟩
      exact ⟨Ne.symm hne, hκ.symm⟩

theorem monochromaticPairs_eq_classPairUnion (κ : V → Fin q) :
    monochromaticPairs κ = classPairUnion κ := by
  ext e
  rw [mem_monochromaticPairs, mem_classPairUnion]

theorem monochromatic_pair_count_identity (κ : V → Fin q) :
    2 * (monochromaticPairs κ).card + Fintype.card V =
      ∑ d, (colourClass κ d).card ^ 2 := by
  rw [monochromaticPairs_eq_classPairUnion]
  exact classPairUnion_count_identity κ

theorem actual_monochromatic_pair_lower_bound (κ : V → Fin q) (hq : 0 < q)
    (hn : 2 * q ≤ Fintype.card V) :
    (Fintype.card V : ℝ) ^ 2 / (4 * (q : ℝ)) ≤ ((monochromaticPairs κ).card : ℝ) := by
  rw [monochromaticPairs_eq_classPairUnion]
  exact classPairUnion_lower_bound κ hq hn

end CCO.ParityHasse.Sparse
