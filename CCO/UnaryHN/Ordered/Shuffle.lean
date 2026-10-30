import CCO.UnaryHN.Ordered.Forget
import Mathlib.Data.Prod.Lex

/-! A genuine finite order amalgam over the WHOLE common ordered base.
The cut/side/rank labels agree at exactly identified base points. Extra
points of the old strong amalgam receive a finite tie-break order too. -/

universe v
namespace CCO.UnaryHN.Native.Ordered

noncomputable def below {H V : Type v} [Fintype H] [LinearOrder V]
    (f : H → V) (x : V) : Finset H := by
  classical
  exact Finset.univ.filter (fun r => f r < x)

noncomputable def cutCount {H V : Type v} [Fintype H] [LinearOrder V]
    (f : H → V) (x : V) : ℕ := (below f x).card

noncomputable def pointRank (V : Type v) [Fintype V] [LinearOrder V] (x : V) : ℕ :=
  cutCount id x

theorem cutCount_mono {H V : Type v} [Fintype H] [LinearOrder V]
    (f : H → V) {x y : V} (hxy : x < y) : cutCount f x ≤ cutCount f y := by
  classical
  apply Finset.card_le_card
  intro r hr
  simp only [below, Finset.mem_filter, Finset.mem_univ, true_and] at hr ⊢
  exact lt_trans hr hxy

theorem cutCount_lt_from_base {H V : Type v} [Fintype H] [LinearOrder V]
    (f : H → V) (r : H) (y : V) (hry : f r < y) :
    cutCount f (f r) < cutCount f y := by
  classical
  apply Finset.card_lt_card
  apply Finset.ssubset_iff.mpr
  refine ⟨r, ?_, ?_⟩
  · simp [below]
  · intro s hs
    simp only [Finset.mem_insert, below, Finset.mem_filter, Finset.mem_univ, true_and] at hs ⊢
    rcases hs with rfl | hs
    · exact hry
    · exact lt_trans hs hry

theorem pointRank_strictMono (V : Type v) [Fintype V] [LinearOrder V] :
    StrictMono (pointRank V) := by
  intro x y hxy
  exact cutCount_lt_from_base id x y hxy

theorem cutCount_at_base {H V : Type v} [Fintype H] [LinearOrder H] [LinearOrder V]
    (f : H → V) (hf : StrictMono f) (r : H) :
    cutCount f (f r) = pointRank H r := by
  classical
  apply congrArg Finset.card
  ext s
  simp only [below, Finset.mem_filter, Finset.mem_univ, true_and]
  exact hf.lt_iff_lt

abbrev ShuffleKey := ℕ ×ₗ (Bool ×ₗ (Bool ×ₗ ℕ))

noncomputable def sideCode {H V : Type v} [Fintype H] [Fintype V] [LinearOrder V]
    (f : H → V) (side : Bool) (x : V) : ShuffleKey := by
  classical
  exact if x ∈ Set.range f then toLex (cutCount f x, toLex (true, toLex (false, 0)))
    else toLex (cutCount f x, toLex (false, toLex (side, pointRank V x)))

theorem sideCode_at_base {H V : Type v} [Fintype H] [Fintype V]
    [LinearOrder H] [LinearOrder V] (f : H → V) (hf : StrictMono f)
    (side : Bool) (r : H) :
    sideCode f side (f r) = toLex (pointRank H r, toLex (true, toLex (false, 0))) := by
  classical
  simp only [sideCode, if_pos (Set.mem_range_self r), cutCount_at_base f hf]

theorem sideCode_strictMono {H V : Type v} [Fintype H] [Fintype V]
    [LinearOrder V] (f : H → V) (side : Bool) : StrictMono (sideCode f side) := by
  classical
  intro x y hxy
  have hle := cutCount_mono f hxy
  by_cases hlt : cutCount f x < cutCount f y
  · unfold sideCode
    split_ifs <;> exact Prod.Lex.toLex_lt_toLex.mpr (Or.inl hlt)
  · have heq : cutCount f x = cutCount f y := le_antisymm hle (le_of_not_gt hlt)
    by_cases hx : x ∈ Set.range f
    · obtain ⟨r, hr⟩ := hx
      have hstrict : cutCount f x < cutCount f y := by
        rw [← hr]
        exact cutCount_lt_from_base f r y (by simpa [hr] using hxy)
      exact (hlt hstrict).elim
    · by_cases hy : y ∈ Set.range f
      · simp only [sideCode, if_neg hx, if_pos hy]
        apply Prod.Lex.toLex_lt_toLex.mpr
        refine Or.inr ⟨heq, ?_⟩
        exact Prod.Lex.toLex_lt_toLex.mpr (Or.inl (by decide))
      · simp only [sideCode, if_neg hx, if_neg hy]
        apply Prod.Lex.toLex_lt_toLex.mpr
        refine Or.inr ⟨heq, ?_⟩
        apply Prod.Lex.toLex_lt_toLex.mpr
        refine Or.inr ⟨rfl, ?_⟩
        exact Prod.Lex.toLex_lt_toLex.mpr (Or.inr ⟨rfl, pointRank_strictMono V hxy⟩)

end CCO.UnaryHN.Native.Ordered
