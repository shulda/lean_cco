import CCO.ParityHasse.Sparse.ConnectedExtraction
import CCO.ParityHasse.Sparse.CycleGraph
import CCO.ParityHasse.Sparse.GraphLaw

/-! The concrete labelled graph conclusion, and its one-label chromatic consumer. -/
namespace CCO.ParityHasse.Sparse

structure SparseLabelledGraph (q r g : ℕ) where
  size : ℕ
  graph : SimpleGraph (Fin size)
  label : Sym2 (Fin size) → Fin r
  noShortCycles : NoShortCycles graph g
  monochromatic : ∀ κ : Fin size → Fin q, ∃ d : Fin q, ∀ i : Fin r,
    ∃ x y, graph.Adj x y ∧ label s(x, y) = i ∧ κ x = d ∧ κ y = d

/-- The r=1 conclusion used by orbital parity. -/
def SparseLabelledGraph.toHighGirthChromatic {q g : ℕ} (W : SparseLabelledGraph q 1 g) :
    HighGirthChromatic q g where
  size := W.size
  graph := W.graph
  noShortCycles := W.noShortCycles
  monochromatic κ := by
    obtain ⟨d, hd⟩ := W.monochromatic κ
    obtain ⟨x, y, hxy, _, hx, hy⟩ := hd ⟨0, by decide⟩
    exact ⟨x, y, hxy, hx.trans hy.symm⟩

/-- Pruning a genuinely labelled edge set preserves the full labelled conclusion
whenever every robust requested-edge set retains one edge. -/
noncomputable def labelledGraph_of_retained_requests {n q r g : ℕ} (hr : 0 < r)
    (ω : EdgeLabelling (Fin n) r) (F : Finset (Sym2 (Fin n)))
    (hFE : F ⊆ presentEdges ω) (hfree : ShortCycleFree g F)
    (hretain : ∀ (κ : Fin n → Fin q) (h : Fin q → Fin r),
      ∃ e ∈ monochromaticPairs κ, e ∈ F ∧ ω e = some (requestedTarget κ h e)) :
    SparseLabelledGraph q r g := by
  classical
  let lbl : Sym2 (Fin n) → Fin r := fun e => (ω e).getD ⟨0, hr⟩
  refine ⟨n, simpleGraphOfEdges F, lbl, noShortCycles_of_shortCycleFree hfree, ?_⟩
  intro κ
  by_contra hbad
  have hbad' : ∀ d : Fin q, ∃ i : Fin r,
      ¬ ∃ x y, (simpleGraphOfEdges F).Adj x y ∧ lbl s(x, y) = i ∧ κ x = d ∧ κ y = d := by
    simpa only [not_exists, not_forall] using hbad
  choose h hh using hbad'
  obtain ⟨e, hmono, heF, heω⟩ := hretain κ h
  obtain ⟨x, y, hne, hκ, rfl⟩ := (mem_monochromaticPairs κ e).1 hmono
  have htarget : requestedTarget κ h s(x, y) = h (κ x) := requestedTarget_pair κ h hκ
  apply hh (κ x)
  refine ⟨x, y, ⟨hne, heF⟩, ?_, rfl, hκ.symm⟩
  dsimp [lbl]
  rw [heω, htarget]
  rfl

end CCO.ParityHasse.Sparse
