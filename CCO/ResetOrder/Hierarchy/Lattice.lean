import Mathlib.Order.Irreducible
import Mathlib.Data.Fintype.Order
import Mathlib.Order.Cover

/-! Complete strict-coarser MI keys determine the actual unique cover. -/
universe u
namespace CCO.ResetOrder.Hierarchy
section Lattice
variable {L : Type u} [Lattice L] [OrderTop L] [Fintype L]

noncomputable def strictUpper (j : L) : Finset L := by
  classical
  exact Finset.univ.filter (fun l => j < l)

@[simp] theorem mem_strictUpper (j l : L) : l ∈ strictUpper j ↔ j < l := by
  classical
  simp [strictUpper]

noncomputable def miParent (j : L) : L := (strictUpper j).inf id

theorem le_miParent (j : L) : j ≤ miParent j := by
  classical
  apply Finset.le_inf
  intro l hl
  exact (mem_strictUpper j l |>.1 hl).le

theorem miParent_le {j l : L} (h : j < l) : miParent j ≤ l := by
  classical
  exact Finset.inf_le ((mem_strictUpper j l).2 h)

theorem lt_miParent {j : L} (hj : InfIrred j) : j < miParent j := by
  apply lt_of_le_of_ne (le_miParent j)
  intro he
  obtain ⟨l, hl, hlEq⟩ := hj.finset_inf_eq he.symm
  have hlt : j < l := (mem_strictUpper j l).1 hl
  exact hlt.ne hlEq.symm

theorem miParent_covBy {j : L} (hj : InfIrred j) : j ⋖ miParent j := by
  rw [covBy_iff_lt_and_eq_or_eq]
  refine ⟨lt_miParent hj, ?_⟩
  intro l hjl hlp
  by_cases h : l = j
  · exact Or.inl h
  · exact Or.inr (le_antisymm hlp (miParent_le (lt_of_le_of_ne hjl (Ne.symm h))))

theorem miParent_unique {j p : L} (hj : InfIrred j) (hp : j ⋖ p) : p = miParent j := by
  have hmin := miParent_le hp.lt
  exact ((hp.eq_or_eq (le_miParent j) hmin).resolve_left (lt_miParent hj).ne').symm

noncomputable def strictCoarserMI (j : L) : Finset L := by
  classical
  exact Finset.univ.filter (fun l => j < l ∧ InfIrred l)

@[simp] theorem mem_strictCoarserMI (j l : L) : l ∈ strictCoarserMI j ↔ j < l ∧ InfIrred l := by
  classical
  simp [strictCoarserMI]

theorem strictCoarserMI_inf (j : L) : (strictCoarserMI j).inf id = miParent j := by
  classical
  apply le_antisymm
  · obtain ⟨s, hs, hmi⟩ := exists_infIrred_decomposition (miParent j)
    rw [← hs]
    apply Finset.le_inf
    intro l hl
    have hp : miParent j ≤ l := hs ▸ Finset.inf_le hl
    by_cases hj : InfIrred j
    · exact Finset.inf_le ((mem_strictCoarserMI j l).2 ⟨(lt_miParent hj).trans_le hp, hmi hl⟩)
    · have hjl : j < l := by
        apply lt_of_le_of_ne ((le_miParent j).trans hp)
        intro he
        exact hj (he.symm ▸ hmi hl)
      exact Finset.inf_le ((mem_strictCoarserMI j l).2 ⟨hjl, hmi hl⟩)
  · apply Finset.le_inf
    intro l hl
    exact miParent_le ((mem_strictCoarserMI j l).1 hl).1

theorem strict_coarser_iff_parent_le {j l : L} (hj : InfIrred j) : j < l ↔ miParent j ≤ l :=
  ⟨miParent_le, fun h => (lt_miParent hj).trans_le h⟩

theorem parent_top_empty_key {j : L} (h : miParent j = ⊤) : strictCoarserMI j = ∅ := by
  classical
  apply Finset.eq_empty_iff_forall_notMem.2
  intro l hl
  obtain ⟨hjl, hmi⟩ := (mem_strictCoarserMI j l).1 hl
  have hlTop : l = ⊤ := top_unique (h ▸ miParent_le hjl)
  exact hmi.ne_top hlTop
end Lattice
end CCO.ResetOrder.Hierarchy
