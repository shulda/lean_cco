import CCO.ParityHasse.Sparse.CycleExpectation
import CCO.ParityHasse.Sparse.GoodOutcome
import CCO.ParityHasse.Sparse.Labelled

/-! The full source sparse labelled graph theorem. All probabilistic and
combinatorial providers in its construction are proved in the imported modules. -/
namespace CCO.ParityHasse.Sparse
noncomputable section

/-- The good random outcome is genuinely pruned, retaining one edge for every
colouring and every requested-label assignment. -/
theorem sparseLabelledOfOutcome {n q r g : ℕ} (hr : 0 < r) {B : ℝ}
    (ω : EdgeLabelling (Fin n) r)
    (hrobust : ∀ (κ : Fin n → Fin q) (h : Fin q → Fin r),
      4 * B < requestedHits (monochromaticPairs κ) (requestedTarget κ h) ω)
    (hcycles : cycleMass g (presentEdges ω) ≤ 4 * B) :
    Nonempty (SparseLabelledGraph q r g) := by
  classical
  obtain ⟨F, hFE, hfree, hdeleted⟩ := delete_short_cycles g (presentEdges ω)
  refine ⟨labelledGraph_of_retained_requests hr ω F hFE hfree ?_⟩
  intro κ h
  let K := Finset.univ.filter (fun e => e ∈ monochromaticPairs κ ∧
    ω e = some (requestedTarget κ h e))
  have hKE : K ⊆ presentEdges ω := by
    intro e he
    obtain ⟨_, hmono, hω⟩ := Finset.mem_filter.mp he
    have hnd := (Finset.mem_filter.mp hmono).2.1
    exact (mem_presentEdges ω e).2 ⟨hnd, by rw [hω]; simp⟩
  have hK : 4 * B < (K.card : ℝ) := by
    simpa only [requestedHits_eq_card] using hrobust κ h
  obtain ⟨e, heK, heF⟩ := bounded_deletion_retains hKE hK (hdeleted.trans hcycles)
  obtain ⟨_, heMono, heLabel⟩ := Finset.mem_filter.mp heK
  exact ⟨e, heMono, heF, heLabel⟩

/-- The source construction for an explicit girth parameter at least three. -/
theorem sparse_labelled_graph_exists_of_three_le {q r g : ℕ}
    (hq : 0 < q) (hr : 0 < r) (hg : 3 ≤ g) :
    Nonempty (SparseLabelledGraph q r g) := by
  let c := sparseConstant q r
  let B := cycleBudget c g
  have hc : 0 < c := sparseConstant_pos hq hr
  have hB : 0 < B := cycleBudget_pos hc hg
  obtain ⟨n, hnsize, hcn, hUnion, hGap⟩ := exists_source_sparse_size hq hr B
  have hn : 0 < n := by omega
  have hExpect := expect_cycleMass_le (g := g) hn hr hc.le hcn.le
  obtain ⟨ω, hrobust, hcycles⟩ := exists_good_outcome
    hq hr hn hnsize hc hcn hB hUnion hGap hExpect
  exact sparseLabelledOfOutcome hr ω hrobust hcycles

/-- Full finite sparse labelled graph theorem, for all positive colour/label
counts and every natural girth parameter. No graph/probability provider remains. -/
theorem sparse_labelled_graph_exists {q r : ℕ} (hq : 0 < q) (hr : 0 < r) (g : ℕ) :
    Nonempty (SparseLabelledGraph q r g) := by
  obtain ⟨W⟩ := sparse_labelled_graph_exists_of_three_le hq hr
    (le_max_right g 3)
  have hs : NoShortCycles W.graph g := by
    intro ℓ hℓ hbound f
    exact W.noShortCycles ℓ hℓ (hbound.trans (le_max_left g 3)) f
  exact ⟨⟨W.size, W.graph, W.label, hs, W.monochromatic⟩⟩

/-- C05 before connected extraction: the r=1 specialization really has no
proper q-colouring. -/
theorem high_girth_chromatic_exists {q : ℕ} (hq : 0 < q) (g : ℕ) :
    Nonempty (HighGirthChromatic q g) := by
  obtain ⟨W⟩ := sparse_labelled_graph_exists hq (by decide : 0 < 1) g
  exact ⟨W.toHighGirthChromatic⟩

/-- The finite connected graph consumed by the SAP-free orbital-parity proof. -/
theorem connected_high_girth_chromatic_exists {q : ℕ} (hq : 0 < q) (g : ℕ) :
    Nonempty (ConnectedHighGirthChromatic q g) := by
  obtain ⟨W⟩ := high_girth_chromatic_exists hq g
  exact ⟨W.connectedExtraction⟩

end
end CCO.ParityHasse.Sparse
