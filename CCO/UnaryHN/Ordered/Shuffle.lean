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
  simp only [sideCode, ite_eq_left (Set.mem_range_self r), cutCount_at_base f hf]

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
      · simp only [sideCode, ite_eq_right hx, ite_eq_left hy]
        apply Prod.Lex.toLex_lt_toLex.mpr
        refine Or.inr ⟨heq, ?_⟩
        exact Prod.Lex.toLex_lt_toLex.mpr (Or.inl (show (false : Bool) < true from by decide))
      · simp only [sideCode, ite_eq_right hx, ite_eq_right hy]
        apply Prod.Lex.toLex_lt_toLex.mpr
        refine Or.inr ⟨heq, ?_⟩
        apply Prod.Lex.toLex_lt_toLex.mpr
        refine Or.inr ⟨rfl, ?_⟩
        exact Prod.Lex.toLex_lt_toLex.mpr (Or.inr ⟨rfl, pointRank_strictMono V hxy⟩)

theorem shuffle_orders {H V W Z : Type v} [Fintype H] [Fintype V] [Fintype W]
    [LinearOrder H] [LinearOrder V] [LinearOrder W] [Finite Z]
    (sL : H → V) (sR : H → W) (hsL : StrictMono sL) (hsR : StrictMono sR)
    (jL : V → Z) (jR : W → Z) (hL : Function.Injective jL) (hR : Function.Injective jR)
    (hOverlap : ∀ x y, jL x = jR y → ∃ r, x = sL r ∧ y = sR r) :
    ∃ o : LinearOrder Z,
      (∀ x y, x < y → @LT.lt Z o.toLT (jL x) (jL y)) ∧
      (∀ x y, x < y → @LT.lt Z o.toLT (jR x) (jR y)) := by
  classical
  let : Fintype Z := Fintype.ofFinite Z
  have hcommon (x : V) (y : W) (hxy : jL x = jR y) :
      sideCode sL false x = sideCode sR true y := by
    obtain ⟨r, rfl, rfl⟩ := hOverlap x y hxy
    rw [sideCode_at_base sL hsL, sideCode_at_base sR hsR]
  let label : Z → ShuffleKey := fun z =>
    if h : ∃ x, jL x = z then sideCode sL false (Classical.choose h)
    else if h' : ∃ y, jR y = z then sideCode sR true (Classical.choose h')
    else toLex (0, toLex (false, toLex (false, 0)))
  have hlabelL (x : V) : label (jL x) = sideCode sL false x := by
    have hx : ∃ a, jL a = jL x := ⟨x, rfl⟩
    simp only [label, dite_eq_left hx]
    exact congrArg (sideCode sL false) (hL (Classical.choose_spec hx))
  have hlabelR (y : W) : label (jR y) = sideCode sR true y := by
    by_cases hx : ∃ x, jL x = jR y
    · simp only [label, dite_eq_left hx]
      exact hcommon (Classical.choose hx) y (Classical.choose_spec hx)
    · have hy : ∃ b, jR b = jR y := ⟨y, rfl⟩
      simp only [label, dite_eq_right hx, dite_eq_left hy]
      exact congrArg (sideCode sR true) (hR (Classical.choose_spec hy))
  let key : Z → ShuffleKey ×ₗ Fin (Fintype.card Z) :=
    fun z => toLex (label z, Fintype.equivFin Z z)
  have hkey : Function.Injective key := by
    intro x y hxy
    exact (Fintype.equivFin Z).injective (congrArg (fun p => (ofLex p).2) hxy)
  let o : LinearOrder Z := LinearOrder.lift' key hkey
  refine ⟨o, ?_, ?_⟩
  · intro x y hxy
    change key (jL x) < key (jL y)
    apply Prod.Lex.toLex_lt_toLex.mpr
    left
    change label (jL x) < label (jL y)
    rw [hlabelL, hlabelL]
    exact sideCode_strictMono sL false hxy
  · intro x y hxy
    change key (jR x) < key (jR y)
    apply Prod.Lex.toLex_lt_toLex.mpr
    left
    change label (jR x) < label (jR y)
    rw [hlabelR, hlabelR]
    exact sideCode_strictMono sR true hxy

end CCO.UnaryHN.Native.Ordered
