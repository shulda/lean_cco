import CCO.RawExact.QuotientPathExpansion

/-!
# The only overlapping private expansion edges are direct paths

Different marked edges cannot contribute the same formal path edge.
If different word occurrences do overlap, both paths are length one
and belong to the SAME canonically oriented marked pair. This is the
structural input for merging their actual source atomic labels.
-/

universe u v w

namespace CCO.RawExact.QuotientExpansion

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {n : Nat} (sort : Fin n → ι) (P : Menus S sort)

/-- A formal marked image can occur only at one of the two word endpoints. -/
theorem mark_position_endpoint
    (o : Occurrence S sort P) (p : PathPosition S (word S sort P o)) (m : Fin n)
    (h : mark S sort P m = atPosition S sort P o p) :
    (p.val = 0 ∧ m = left o.1) ∨
      (p.val = diversityLength S (word S sort P o) ∧ m = right o.1) := by
  unfold atPosition at h
  split_ifs at h with hp0 hpEnd
  · exact Or.inl ⟨hp0, Sum.inl.inj h⟩
  · exact Or.inr ⟨hpEnd, Sum.inl.inj h⟩
  · cases h

/-- A shared position of two DIFFERENT occurrences is a marked vertex. -/
theorem shared_position_is_marked
    (o o' : Occurrence S sort P) (hDifferent : o ≠ o')
    (p : PathPosition S (word S sort P o))
    (p' : PathPosition S (word S sort P o'))
    (h : atPosition S sort P o p = atPosition S sort P o' p') :
    ∃ m, atPosition S sort P o p = mark S sort P m := by
  by_cases hp0 : p.val = 0
  · refine ⟨left o.1, ?_⟩
    simp [atPosition, hp0]
  · by_cases hpEnd : p.val = diversityLength S (word S sort P o)
    · refine ⟨right o.1, ?_⟩
      simp only [atPosition, dite_eq_right hp0, dite_eq_left hpEnd]
    · let pp : Interior S sort P o := ⟨p, hp0, hpEnd⟩
      have hPrivate : interior S sort P o pp = atPosition S sort P o' p' :=
        (at_interior S sort P o pp).symm.trans h
      exact False.elim (hDifferent (interior_occurrence_unique S sort P o o' pp p' hPrivate))

/-- An edge whose two ends are marked must be a direct one-letter path. -/
theorem path_edge_between_marks
    (o : Occurrence S sort P)
    (p q : PathPosition S (word S sort P o))
    (hpq : pathAdjacent S (word S sort P o) p q)
    (m r : Fin n)
    (hm : mark S sort P m = atPosition S sort P o p)
    (hr : mark S sort P r = atPosition S sort P o q) :
    diversityLength S (word S sort P o) = 1 ∧
      ((m = left o.1 ∧ r = right o.1) ∨ (m = right o.1 ∧ r = left o.1)) := by
  have hPositions : p ≠ q := pathAdjacent_ne S _ p q hpq
  rcases mark_position_endpoint S sort P o p m hm with hp | hp <;>
    rcases mark_position_endpoint S sort P o q r hr with hq | hq
  · have heq : p = q := Fin.ext (hp.1.trans hq.1.symm)
    exact False.elim (hPositions heq)
  · refine ⟨?_, Or.inl ⟨hp.2, hq.2⟩⟩
    rcases hpq with h | h <;> omega
  · refine ⟨?_, Or.inr ⟨hp.2, hq.2⟩⟩
    rcases hpq with h | h <;> omega
  · have heq : p = q := Fin.ext (hp.1.trans hq.1.symm)
    exact False.elim (hPositions heq)

/-- Canonical orientation prevents a pair from being a different
marked edge when its two endpoints agree in either orientation. -/
theorem edge_eq_of_unordered_endpoints (e f : Edge n)
    (h : (left e = left f ∧ right e = right f) ∨
      (left e = right f ∧ right e = left f)) : e = f := by
  rcases h with h | h
  · apply Subtype.ext
    exact Prod.ext h.1 h.2
  · have he := e.property
    have hf := f.property
    change left e < right e at he
    change left f < right f at hf
    rw [h.1, h.2] at he
    exact False.elim ((lt_asymm he hf))

/-- The only overlap between different original word occurrences is
one direct edge for the same underlying marked pair. -/
theorem different_overlapping_edges_are_same_direct_edge
    (o o' : Occurrence S sort P) (hDifferent : o ≠ o')
    (p q : PathPosition S (word S sort P o))
    (p' q' : PathPosition S (word S sort P o'))
    (hpq : pathAdjacent S (word S sort P o) p q)
    (hpq' : pathAdjacent S (word S sort P o') p' q')
    (hp : atPosition S sort P o p = atPosition S sort P o' p')
    (hq : atPosition S sort P o q = atPosition S sort P o' q') :
    o.1 = o'.1 ∧ diversityLength S (word S sort P o) = 1 ∧
      diversityLength S (word S sort P o') = 1 := by
  obtain ⟨m, hm⟩ := shared_position_is_marked S sort P o o' hDifferent p p' hp
  obtain ⟨r, hr⟩ := shared_position_is_marked S sort P o o' hDifferent q q' hq
  have hm' : mark S sort P m = atPosition S sort P o' p' := hm.symm.trans hp
  have hr' : mark S sort P r = atPosition S sort P o' q' := hr.symm.trans hq
  obtain ⟨hLen, hEnds⟩ := path_edge_between_marks S sort P o p q hpq m r hm.symm hr.symm
  obtain ⟨hLen', hEnds'⟩ := path_edge_between_marks S sort P o' p' q' hpq' m r hm' hr'
  refine ⟨?_, hLen, hLen'⟩
  apply edge_eq_of_unordered_endpoints
  rcases hEnds with h | h <;> rcases hEnds' with h' | h'
  · exact Or.inl ⟨h.1.symm.trans h'.1, h.2.symm.trans h'.2⟩
  · exact Or.inr ⟨h.1.symm.trans h'.1, h.2.symm.trans h'.2⟩
  · exact Or.inr ⟨h.2.symm.trans h'.2, h.1.symm.trans h'.1⟩
  · exact Or.inl ⟨h.2.symm.trans h'.2, h.1.symm.trans h'.1⟩

end CCO.RawExact.QuotientExpansion
