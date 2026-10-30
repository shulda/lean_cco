import CCO.UnaryFreshFrames.Quotient.System

/-! AFF is constructed BEFORE any homogeneity or real-base orbit premise.
The construction covers all hidden A points, including orphan quotient points.
Every nonreal representative avoids B and all earlier chosen real generators. -/
universe u v
namespace CCO.UnaryFreshFrames.Structure
variable {L : Language.{u}} {V : Type v} (H : Structure L V)

/-- C28–C33: actual real representatives give the exact fresh-frame equation.
Only the named representations, actual subgroup transitivity, finite singleton
closures and the two kernel clauses are used. -/
theorem quotient_system_fresh_frame {real : Set L.Sorts} (S : H.NamedQuotientSystem real)
    (G : Subgroup H.Aut) (ht : S.SourceTransitive G)
    (hfinite : ∀ x : V, (H.closureAt x).Finite) (hkernel : S.KernelClauses)
    (A B : Set V) (hA : A.Finite) (hAcl : H.Closed A) (hB : B.Finite) (hAB : A ⊆ B) :
    ∃ D : Set V, D.Finite ∧ D ⊆ {x | H.sort x ∈ real} ∧
      A ⊆ H.closure D ∧ H.closure D ∩ B = A := by
  classical
  have hcover : ∀ F : Finset V, (F : Set V) ⊆ A →
      ∃ D : Finset V, (∀ x ∈ D, H.sort x ∈ real) ∧
        (F : Set V) ⊆ H.closure (D : Set V) ∧ H.closure (D : Set V) ∩ B ⊆ A := by
    intro F
    induction F using Finset.induction_on with
    | empty =>
      intro _
      refine ⟨∅, fun _ h => False.elim (Finset.notMem_empty _ h), ?_, ?_⟩
      · rw [Finset.coe_empty]
        exact Set.empty_subset _
      · rw [Finset.coe_empty, H.closure_empty]
        exact fun _ h => False.elim h.1
    | @insert b F hb ih =>
      intro hFA
      have hbA : b ∈ A := hFA (Finset.mem_insert_self b F)
      obtain ⟨D, hDreal, hDcover, hDinter⟩ := ih (by
        intro x hx
        exact hFA (Finset.mem_insert_of_mem hx))
      have hbclA : H.closureAt b ⊆ A := H.closure_minimal hAcl
        (by intro z hz; exact hz ▸ hbA)
      obtain ⟨x, hxreal, hbx, hxinter⟩ : ∃ x : V,
          H.sort x ∈ real ∧ b ∈ H.closureAt x ∧ H.closureAt x ∩ B ⊆ A := by
        by_cases hbR : H.sort b ∈ real
        · exact ⟨b, hbR, H.subset_closure {b} rfl, fun _ h => hbclA h.1⟩
        · obtain ⟨x, hreal, hbx, heq, _⟩ := S.representative G ht hfinite hkernel b hbR
            (B ∪ (D : Set V)) (hB.union D.finite_toSet)
          refine ⟨x, hreal, hbx, ?_⟩
          intro y hy
          have hz : y ∈ H.closureAt x ∩ (B ∪ (D : Set V)) := ⟨hy.1, Or.inl hy.2⟩
          rw [heq] at hz
          exact hbclA hz.1
      have hnew : H.closure (↑(insert x D) : Set V) =
          H.closureAt x ∪ H.closure (D : Set V) := by
        rw [Finset.coe_insert, Set.insert_eq, H.closure_union]
        rfl
      refine ⟨insert x D, ?_, ?_, ?_⟩
      · intro y hy
        rcases Finset.mem_insert.mp hy with rfl | hy
        · exact hxreal
        · exact hDreal y hy
      · rw [hnew]
        intro y hy
        rcases Finset.mem_insert.mp hy with rfl | hy
        · exact Or.inl hbx
        · exact Or.inr (hDcover hy)
      · rw [hnew]
        rintro y ⟨hy | hy, hyB⟩
        · exact hxinter ⟨hy, hyB⟩
        · exact hDinter ⟨hy, hyB⟩
  obtain ⟨D, hDreal, hDcover, hDinter⟩ := hcover hA.toFinset
    (fun _ hx => hA.mem_toFinset.mp hx)
  have hgen : A ⊆ H.closure (D : Set V) := fun _ hx => hDcover (hA.mem_toFinset.mpr hx)
  exact ⟨D, D.finite_toSet, hDreal, hgen,
    Set.Subset.antisymm hDinter (fun _ hx => ⟨hgen hx, hAB hx⟩)⟩

end CCO.UnaryFreshFrames.Structure
