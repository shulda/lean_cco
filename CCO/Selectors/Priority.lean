import CCO.Selectors.SourceSelectors
import Lean.Elab.Tactic.Omega

/-!
# Global filter-gate incidence scores

Every score is calculated on an **original** finite atom palette using one
tagged filter family selected for the whole stage, not separately for each
input menu. No SAP, CCO, NR2, PC or terminality is needed for these finite-set
identities. They implement the source's FG incidence lemma.
-/

universe u v w
namespace CCO.Selectors

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)

/-- Filter members incident with a fixed original atom (including non-active
menus); the global filter is independent of the current menu. -/
noncomputable def filtersThrough (F : Family S) {i j : ι}
    (a : S.Atom i j) : Finset (S.Menu i j) := by
  classical
  exact Finset.univ.filter fun A =>
    (⟨i,j,A⟩ : TaggedMenu S) ∈ F ∧ a ∈ A

/-- The number of original tagged filter members containing this atom. -/
noncomputable def incidenceScore (F : Family S) {i j : ι}
    (a : S.Atom i j) : Nat :=
  (filtersThrough S F a).card

theorem mem_filtersThrough {F : Family S} {i j : ι}
    {a : S.Atom i j} {A : S.Menu i j} :
    A ∈ filtersThrough S F a ↔
      (⟨i,j,A⟩ : TaggedMenu S) ∈ F ∧ a ∈ A := by
  classical
  simp [filtersThrough]

theorem filtersThrough_subset_active (F : Family S)
    {i j : ι} (D : S.Menu i j) {a : S.Atom i j} (ha : a ∈ D) :
    filtersThrough S F a ⊆ active S F D := by
  intro A hA
  obtain ⟨hAF, haA⟩ := (mem_filtersThrough S).mp hA
  exact (mem_active S).mpr ⟨hAF,⟨a,haA,ha⟩⟩

theorem filtersThrough_eq_active_of_gate_mem (F : Family S)
    {i j : ι} {D : S.Menu i j} {a : S.Atom i j}
    (ha : a ∈ gate S F D) :
    filtersThrough S F a = active S F D := by
  apply Finset.Subset.antisymm
  · exact filtersThrough_subset_active S F D ha.1
  · intro A hA
    obtain ⟨hAF,hMeet⟩ := (mem_active S).mp hA
    exact (mem_filtersThrough S).mpr ⟨hAF,ha.2 A hAF hMeet⟩

/-- Incidence never exceeds the number of filter members active on the
present menu. This bound does not depend on any visibility assumption. -/
theorem incidenceScore_le_active (F : Family S)
    {i j : ι} (D : S.Menu i j) {a : S.Atom i j} (ha : a ∈ D) :
    incidenceScore S F a ≤ (active S F D).card := by
  exact Finset.card_le_card (filtersThrough_subset_active S F D ha)

/-- The gate consists precisely of atoms reaching the active-list bound.
This equivalence remains valid even when the gate is empty. -/
theorem mem_gate_iff_incidenceScore_eq_active (F : Family S)
    {i j : ι} (D : S.Menu i j) (a : S.Atom i j) :
    a ∈ gate S F D ↔
      a ∈ D ∧ incidenceScore S F a = (active S F D).card := by
  constructor
  · intro ha
    exact ⟨ha.1, congrArg Finset.card
      (filtersThrough_eq_active_of_gate_mem S F ha)⟩
  · rintro ⟨haD,hcount⟩
    have hsubset := filtersThrough_subset_active S F D haD
    have hcard : (active S F D).card ≤ (filtersThrough S F a).card := by
      change (active S F D).card ≤ incidenceScore S F a
      exact le_of_eq hcount.symm
    have heq : filtersThrough S F a = active S F D :=
      Finset.eq_of_subset_of_card_le hsubset hcard
    refine ⟨haD,?_⟩
    intro A hAF hMeet
    have hactive : A ∈ active S F D := (mem_active S).mpr ⟨hAF,hMeet⟩
    rw [← heq] at hactive
    exact ((mem_filtersThrough S).mp hactive).2

/-- The source FG lemma: a nonempty global gate is exactly the argmax of
its fixed original-atom incidence score, with equality of sets. -/
theorem gate_eq_incidence_argmax (F : Family S)
    {i j : ι} (D : S.Menu i j) (hnonempty : (gate S F D).Nonempty) :
    gate S F D =
      {a | a ∈ D ∧ ∀ b ∈ D, incidenceScore S F b ≤ incidenceScore S F a} := by
  ext a
  constructor
  · intro ha
    have hcount := (mem_gate_iff_incidenceScore_eq_active S F D a).mp ha
    refine ⟨hcount.1,?_⟩
    intro b hbD
    exact (incidenceScore_le_active S F D hbD).trans (le_of_eq hcount.2.symm)
  · rintro ⟨haD,hmax⟩
    obtain ⟨c,hcGate⟩ := hnonempty
    have hcCount := (mem_gate_iff_incidenceScore_eq_active S F D c).mp hcGate
    have hle := incidenceScore_le_active S F D haD
    have hge := hmax c hcCount.1
    have hcount : incidenceScore S F a = (active S F D).card := by
      omega
    exact (mem_gate_iff_incidenceScore_eq_active S F D a).mpr ⟨haD,hcount⟩

/-- A discarded original atom has strictly smaller score than every
survivor, not merely a weak score inequality. -/
theorem incidenceScore_strict_of_gate (F : Family S)
    {i j : ι} (D : S.Menu i j) {a b : S.Atom i j}
    (ha : a ∈ gate S F D) (hbD : b ∈ D)
    (hb : b ∉ gate S F D) :
    incidenceScore S F b < incidenceScore S F a := by
  have haCount := (mem_gate_iff_incidenceScore_eq_active S F D a).mp ha
  have hle := incidenceScore_le_active S F D hbD
  have hne : incidenceScore S F b ≠ (active S F D).card := by
    intro heq
    exact hb ((mem_gate_iff_incidenceScore_eq_active S F D b).mpr ⟨hbD,heq⟩)
  omega

end CCO.Selectors
