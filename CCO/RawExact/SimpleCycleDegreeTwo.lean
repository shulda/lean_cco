import CCO.RawExact.CycleIncidence

/-!
# Whole-edge incidence at degree-two vertices of a genuine simple cycle

The cycle contains two DISTINCT neighbours of each of its vertices. If
these exhaust the ambient graph's possible neighbours there, both actual
ambient edges are traversed by the cycle. This is the local statement
needed to propagate a private-path segment to both marked endpoints.
-/

universe u v w z

namespace CCO.RawExact

/-- A cyclic successor permutation on at least three positions
cannot exchange just two positions. -/
theorem cyclicNext_no_two_cycle {n : Nat} (hn : 0 < n) (hThree : 3 ≤ n)
    (p q : Fin n) (hpq : cyclicNext hn p = q) (hqp : cyclicNext hn q = p) : False := by
  have hp := p.isLt
  have hq := q.isLt
  have h1 : (p.val + 1) % n = q.val := congrArg Fin.val hpq
  have h2 : (q.val + 1) % n = p.val := congrArg Fin.val hqp
  by_cases hpEnd : p.val + 1 = n
  · rw [hpEnd, Nat.mod_self] at h1
    have hqZero : q.val = 0 := h1.symm
    rw [hqZero, Nat.zero_add, Nat.mod_eq_of_lt (by omega : 1 < n)] at h2
    omega
  · rw [Nat.mod_eq_of_lt (by omega : p.val + 1 < n)] at h1
    by_cases hqEnd : q.val + 1 = n
    · rw [hqEnd, Nat.mod_self] at h2
      omega
    · rw [Nat.mod_eq_of_lt (by omega : q.val + 1 < n)] at h2
      omega

variable {ι : Type u} {X : ι → Type v}
variable {S : AtomicSource.{u,v,w} ι X} {V : Type z}
variable {D : PartialDiagram S V}

/-- A literal formal vertex occurs in the injective cycle enumeration. -/
def CycleVertex (C : SimpleCycle D) (v : V) : Prop := ∃ p, C.vertices p = v

/-- A literal unoriented edge is traversed by the cycle, rather than
merely joining two vertices that happen to belong to its support. -/
def CycleEdge (C : SimpleCycle D) (v w : V) : Prop :=
  ∃ p, (C.vertices p = v ∧ C.vertices (cyclicNext C.length_pos p) = w) ∨
    (C.vertices p = w ∧ C.vertices (cyclicNext C.length_pos p) = v)

theorem cycleEdge_symm (C : SimpleCycle D) (v w : V) :
    CycleEdge C v w ↔ CycleEdge C w v := by
  constructor <;> rintro ⟨p, h | h⟩
  · exact ⟨p, Or.inr h⟩
  · exact ⟨p, Or.inl h⟩
  · exact ⟨p, Or.inr h⟩
  · exact ⟨p, Or.inl h⟩

theorem cycleEdge_vertices (C : SimpleCycle D) {v w : V}
    (h : CycleEdge C v w) : CycleVertex C v ∧ CycleVertex C w := by
  obtain ⟨p, h | h⟩ := h
  · exact ⟨⟨p, h.1⟩, ⟨cyclicNext C.length_pos p, h.2⟩⟩
  · exact ⟨⟨cyclicNext C.length_pos p, h.2⟩, ⟨p, h.1⟩⟩

theorem cycleEdge_adjacent (C : SimpleCycle D)
    (Adj : V → V → Prop)
    (hSymm : ∀ v w, Adj v w → Adj w v)
    (hEdges : ∀ p, Adj (C.vertices p) (C.vertices (cyclicNext C.length_pos p)))
    {v w : V} (h : CycleEdge C v w) : Adj v w := by
  obtain ⟨p, h | h⟩ := h
  · rw [← h.1, ← h.2]
    exact hEdges p
  · rw [← h.1, ← h.2]
    exact hSymm _ _ (hEdges p)

/-- The actual incoming and outgoing cycle neighbours are distinct;
this uses the ≥3 condition, not merely the existence of two edges. -/
theorem cycle_two_distinct_neighbours (C : SimpleCycle D) (v : V)
    (hOn : CycleVertex C v) :
    ∃ before after : V, before ≠ after ∧ CycleEdge C v before ∧ CycleEdge C v after := by
  obtain ⟨p, hp⟩ := hOn
  obtain ⟨prev, hprev⟩ := cyclicNext_surjective C.length_pos p
  refine ⟨C.vertices prev, C.vertices (cyclicNext C.length_pos p), ?_, ?_, ?_⟩
  · intro heq
    have hIndex : prev = cyclicNext C.length_pos p := C.vertices.injective heq
    exact cyclicNext_no_two_cycle C.length_pos C.length_ge_three p prev hIndex.symm hprev
  · exact ⟨prev, Or.inr ⟨rfl, (congrArg C.vertices hprev).trans hp⟩⟩
  · exact ⟨p, Or.inl ⟨hp, rfl⟩⟩

/-- At an ambient degree-two vertex on the cycle, BOTH possible
ambient edges occur as actual cycle edges. -/
theorem cycle_degree_two_edges (C : SimpleCycle D)
    (Adj : V → V → Prop)
    (hSymm : ∀ v w, Adj v w → Adj w v)
    (hEdges : ∀ p, Adj (C.vertices p) (C.vertices (cyclicNext C.length_pos p)))
    (v a b : V)
    (hExhaust : ∀ q, Adj v q → q = a ∨ q = b)
    (hOn : CycleVertex C v) : CycleEdge C v a ∧ CycleEdge C v b := by
  obtain ⟨before, after, hDifferent, hBefore, hAfter⟩ := cycle_two_distinct_neighbours C v hOn
  have hBeforeCases := hExhaust before (cycleEdge_adjacent C Adj hSymm hEdges hBefore)
  have hAfterCases := hExhaust after (cycleEdge_adjacent C Adj hSymm hEdges hAfter)
  rcases hBeforeCases with hba | hbb <;> rcases hAfterCases with haa | hab'
  · exact False.elim (hDifferent (hba.trans haa.symm))
  · exact ⟨hba ▸ hBefore, hab' ▸ hAfter⟩
  · exact ⟨haa ▸ hAfter, hbb ▸ hBefore⟩
  · exact False.elim (hDifferent (hbb.trans hab'.symm))

end CCO.RawExact
