import CCO.ParityHasse.Original.HasseInduction

/-! Finite chain indices are powers of two, including the equality interval. -/
universe u
namespace CCO.ParityHasse.Original

theorem relativeIndicesPowerTwo {L : Type u} [PartialOrder L]
    [WellFoundedLT L] [IsStronglyCoatomic L] (idx : L → L → Nat)
    (diagonal : ∀ E, idx E E = 1)
    (multiply : ∀ E D F, E ≤ D → D ≤ F → idx E F ≠ 0 →
      idx E F = idx E D * idx D F)
    (coverTwo : ∀ E F, E ⋖ F → idx E F ≠ 0 → idx E F = 2) :
    ∀ E F, E ≤ F → idx E F ≠ 0 → ∃ n : Nat, idx E F = 2^n := by
  intro E F
  induction F using WellFoundedLT.induction generalizing E with
  | ind F ih =>
    intro hEF hfin
    rcases hEF.eq_or_lt with rfl | hlt
    · exact ⟨0, by simpa using diagonal E⟩
    · obtain ⟨Y,hEY,hYF⟩ := hlt.exists_le_covby
      have hm := multiply E Y F hEY hYF.le hfin
      have hl : idx E Y ≠ 0 := by
        intro hz
        exact hfin (by rw [hm,hz,Nat.zero_mul])
      have hr : idx Y F ≠ 0 := by
        intro hz
        exact hfin (by rw [hm,hz,Nat.mul_zero])
      obtain ⟨n,hn⟩ := ih Y hYF.lt E hEY hl
      refine ⟨n+1, ?_⟩
      rw [hm,hn,coverTwo Y F hYF hr,pow_succ]

end CCO.ParityHasse.Original
