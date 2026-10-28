import CCO.ParityHasse.Sparse.LabelLaw
import CCO.ParityHasse.Sparse.Cycles
import CCO.ParityHasse.Sparse.ColourCounts
import CCO.ParityHasse.Sparse.Statements

/-! Actual finite random labelled simple graphs, with one independent label per
unordered pair. Labels on the diagonal are ignored. -/
open scoped BigOperators
namespace CCO.ParityHasse.Sparse
noncomputable section

universe u
variable {V : Type u} [Fintype V] [DecidableEq V] {r q : ℕ}

abbrev EdgeLabelling (V : Type u) (r : ℕ) := Sym2 V → Option (Fin r)

def presentEdges (ω : EdgeLabelling V r) : Finset (Sym2 V) :=
  Finset.univ.filter (fun e => ¬ e.IsDiag ∧ ω e ≠ none)

@[simp] theorem mem_presentEdges (ω : EdgeLabelling V r) (e : Sym2 V) :
    e ∈ presentEdges ω ↔ ¬ e.IsDiag ∧ ω e ≠ none := by simp [presentEdges]

def labelledGraph (ω : EdgeLabelling V r) : SimpleGraph V where
  Adj x y := x ≠ y ∧ ω s(x, y) ≠ none
  symm.symm := by intro x y h; simpa only [Sym2.eq_swap] using And.intro h.1.symm h.2
  loopless.irrefl := by intro x h; exact h.1 rfl

@[simp] theorem labelledGraph_adj (ω : EdgeLabelling V r) (x y : V) :
    (labelledGraph ω).Adj x y ↔ s(x, y) ∈ presentEdges ω := by
  simp [labelledGraph, Sym2.mk_isDiag_iff]

/-- Choose the requested label from the common colour of a monochromatic pair.
The arbitrary unordered-pair representative has that same colour. -/
def requestedTarget (κ : V → Fin q) (h : Fin q → Fin r) (e : Sym2 V) : Fin r :=
  h (κ e.out.1)

theorem requestedTarget_pair (κ : V → Fin q) (h : Fin q → Fin r) {x y : V}
    (hxy : κ x = κ y) : requestedTarget κ h s(x, y) = h (κ x) := by
  unfold requestedTarget
  rcases Sym2.mem_iff.mp (Sym2.out_fst_mem s(x, y)) with hx | hy
  · rw [hx]
  · rw [hy, hxy]

/-- An injective cyclic code of length at least three has no diagonal edge. -/
theorem cyclicEdges_not_diag {ℓ : ℕ} [NeZero ℓ] (hℓ : 3 ≤ ℓ)
    (f : CycleCode V ℓ) {e : Sym2 V} (he : e ∈ cyclicEdges f) : ¬ e.IsDiag := by
  obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp he
  simp only [Sym2.mk_isDiag_iff]
  intro h
  have hj := f.injective h
  have h1 : (1 : ZMod ℓ) = 0 := by
    have hh := congrArg (fun k : ZMod ℓ => k - j) hj
    simpa using hh.symm
  apply zmod_two_ne_zero hℓ
  calc
    (2 : ZMod ℓ) = 1 + 1 := by ring
    _ = 0 := by rw [h1]; ring

theorem cycle_supported_iff_positive {ℓ : ℕ} [NeZero ℓ] (hℓ : 3 ≤ ℓ)
    (f : CycleCode V ℓ) (ω : EdgeLabelling V r) :
    cyclicEdges f ⊆ presentEdges ω ↔ ∀ e ∈ cyclicEdges f, ω e ≠ none := by
  constructor
  · intro h e he
    exact ((mem_presentEdges ω e).1 (h he)).2
  · intro h e he
    exact (mem_presentEdges ω e).2 ⟨cyclicEdges_not_diag hℓ f he, h e he⟩

theorem cycle_probability {r ℓ : ℕ} (hr : 0 < r) [NeZero ℓ]
    (hℓ : 3 ≤ ℓ) {ρ : ℝ} (hρ : 0 ≤ ρ) (hρ1 : ρ ≤ 1)
    (f : CycleCode V ℓ) :
    (labelLaw (I := Sym2 V) hr hρ hρ1).prob
      (fun ω => cyclicEdges f ⊆ presentEdges ω) = ρ ^ ℓ := by
  rw [(labelLaw (I := Sym2 V) hr hρ hρ1).prob_congr
    (fun ω => cycle_supported_iff_positive hℓ f ω)]
  rw [positive_labels_probability hr hρ hρ1, cyclicEdges_card hℓ]

end
end CCO.ParityHasse.Sparse
