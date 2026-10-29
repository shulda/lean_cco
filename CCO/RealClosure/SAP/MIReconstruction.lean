import Mathlib.Order.Irreducible
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.EquivFin

/-!
# Proper meet-irreducible coordinates in an arbitrary finite lattice

The separation and reconstruction use only finite infima, with the empty
infimum equal to top. In particular no distributivity, symmetry, source
homogeneity or cycle-completion premise occurs here (B012 C22).
-/

namespace CCO.RealClosure.SAP.FiniteLattice

variable {L : Type*} [SemilatticeInf L] [OrderTop L] [Finite L]

/-- The standard irreducible predicate is precisely proper binary meet
irreducibility; top is excluded even in the one-element lattice. -/
theorem proper_mi_iff (J : L) :
    InfIrred J ↔ J ≠ ⊤ ∧ ∀ A B : L, A ⊓ B = J → A = J ∨ B = J := by
  constructor
  · intro h
    exact ⟨h.ne_top, fun _ _ hab => h.2 hab⟩
  · rintro ⟨hne, h⟩
    refine ⟨fun hmax => hne hmax.eq_top, ?_⟩
    intro A B hab
    exact h A B hab

/-- If `Y` is not below `X`, a proper meet-irreducible above `X`
still separates it from `Y`. The finite irreducible decomposition supplies
the witness without a distributivity assumption. -/
theorem exists_mi_separating {X Y : L} (hYX : ¬Y ≤ X) :
    ∃ J : L, X ≤ J ∧ ¬Y ≤ J ∧ InfIrred J := by
  classical
  obtain ⟨s, hs, hirr⟩ := exists_infIrred_decomposition X
  by_contra h
  apply hYX
  rw [← hs]
  apply Finset.le_inf
  intro J hJ
  by_contra hYJ
  apply h
  refine ⟨J, ?_, hYJ, hirr hJ⟩
  have hle : s.inf id ≤ J := Finset.inf_le hJ
  simpa only [hs] using hle

/-- Order is reconstructed from all proper MI coordinates above `X`. -/
theorem le_iff_forall_mi (X Y : L) :
    Y ≤ X ↔ ∀ J : L, X ≤ J → InfIrred J → Y ≤ J := by
  constructor
  · intro hYX J hXJ _
    exact hYX.trans hXJ
  · intro h
    by_contra hYX
    obtain ⟨J, hXJ, hYJ, hJ⟩ := exists_mi_separating hYX
    exact hYJ (h J hXJ hJ)

/-- The meet of every proper MI above `X`, including the empty top case. -/
noncomputable def miMeet (X : L) : L := by
  classical
  letI := Fintype.ofFinite L
  exact (Finset.univ.filter fun J : L => X ≤ J ∧ InfIrred J).inf id

theorem miMeet_eq (X : L) : miMeet X = X := by
  classical
  letI := Fintype.ofFinite L
  unfold miMeet
  apply le_antisymm
  · apply (le_iff_forall_mi X _).mpr
    intro J hXJ hJ
    exact Finset.inf_le (Finset.mem_filter.mpr ⟨Finset.mem_univ J, hXJ, hJ⟩)
  · apply Finset.le_inf
    intro J hJ
    exact (Finset.mem_filter.mp hJ).2.1

/-- If there are no proper MI coordinates above `X`, reconstruction returns top. -/
theorem eq_top_of_no_mi (X : L) (h : ∀ J : L, X ≤ J → ¬InfIrred J) : X = ⊤ := by
  apply top_le_iff.mp
  apply (le_iff_forall_mi X ⊤).mpr
  intro J hXJ hJ
  exact (h J hXJ hJ).elim

section Monolith

variable [OrderBot L]

/-- A least nonbottom element is below precisely the nonbottom elements. -/
theorem monolith_le_iff_ne_bot {m : L} (hm : m ≠ ⊥)
    (hle : ∀ J : L, J ≠ ⊥ → m ≤ J) (J : L) :
    m ≤ J ↔ J ≠ ⊥ := by
  constructor
  · intro h hJ
    exact hm (le_bot_iff.mp (h.trans hJ.le))
  · exact hle J

/-- Above a nonbottom monolith, the proper MI family is exactly the
proper nonidentity family. This excludes identity even when it is MI. -/
theorem monolith_mi_family {m : L} (hm : m ≠ ⊥)
    (hle : ∀ J : L, J ≠ ⊥ → m ≤ J) (J : L) :
    (m ≤ J ∧ InfIrred J) ↔ (J ≠ ⊥ ∧ InfIrred J) := by
  rw [monolith_le_iff_ne_bot hm hle]

end Monolith

end CCO.RealClosure.SAP.FiniteLattice
