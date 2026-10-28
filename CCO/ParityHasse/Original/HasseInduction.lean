import CCO.ParityHasse.Original.Transposition

/-! The full-lattice Hasse induction, separate from the source parity seed. -/
universe u
namespace CCO.ParityHasse.Original

theorem finiteRelativeHasseInduction {L : Type u} [Lattice L]
    [IsModularLattice L] [WellFoundedLT L] (idx : L → L → Nat)
    (transpose : ∀ E X, idx (E ⊓ X) X = idx E (E ⊔ X))
    (seed : ∀ E F, E ⋖ F → idx E F ≠ 0 →
      ∃ Y X, Y ⋖ X ∧ X ≤ F ∧ ¬X ≤ E ∧ idx Y X = 2) :
    ∀ E F, E ⋖ F → idx E F ≠ 0 → idx E F = 2 := by
  intro E F
  induction F using WellFoundedLT.induction generalizing E with
  | ind F ih =>
    intro hEF hfin
    obtain ⟨Y,X,hYX,hXF,hXE,hidx⟩ := seed E F hEF hfin
    have hsup : E ⊔ X = F := by
      refine (hEF.eq_or_eq le_sup_left (sup_le hEF.le hXF)).resolve_left ?_
      intro h
      apply hXE
      rw [← h]
      exact le_sup_right
    have hKX : E ⊓ X ⋖ X :=
      (transposition_cover_iff E X).mpr (by simpa [hsup] using hEF)
    have hi : idx (E ⊓ X) X = idx E F := by rw [transpose, hsup]
    by_cases hK : E ⊓ X = Y
    · calc
        idx E F = idx (E ⊓ X) X := hi.symm
        _ = 2 := by simpa [hK] using hidx
    · have hjoin : (E ⊓ X) ⊔ Y = X := hKX.wcovBy.sup_eq hYX.wcovBy hK
      have hLY : (E ⊓ X) ⊓ Y ⋖ Y :=
        (transposition_cover_iff (E ⊓ X) Y).mpr (by simpa [hjoin] using hKX)
      have hi' : idx ((E ⊓ X) ⊓ Y) Y = idx E F := by rw [transpose, hjoin, hi]
      have hYF : Y < F := lt_of_lt_of_le hYX.lt hXF
      calc
        idx E F = idx ((E ⊓ X) ⊓ Y) Y := hi'.symm
        _ = 2 := ih Y hYF ((E ⊓ X) ⊓ Y) hLY (by simpa [hi'] using hfin)

end CCO.ParityHasse.Original
