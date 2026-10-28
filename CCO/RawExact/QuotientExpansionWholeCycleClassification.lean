import CCO.RawExact.QuotientExpansionThetaChoices

/-!
# C26: literal two-WHOLE-path cycles or a genuine marked simple cycle

The two-mark alternative is the equality of BOTH vertex support and
traversed unoriented edge support with two DISTINCT original private
word occurrences. The other alternative is the already proved genuine
simple cycle on distinct marks, preserving every original used label.
-/

universe u v w
namespace CCO.RawExact.QuotientExpansion
variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {n : Nat} (sort : Fin n → ι) (P : Menus S sort)
variable (hNonempty : ∀ e, TRel.Nonempty (evaluate S (P e)))
variable (C : SimpleCycle (diagram S sort P hNonempty))

/-- Every traversed edge belongs to one of the selected TWO actual words. -/
theorem TwoMarkChoices.cycle_edge_covered {e : Edge n}
    (choice : TwoMarkChoices S sort P hNonempty C e)
    (hAll : ∀ f, CyclicSuppression.LabelOn (initialCycle S sort P hNonempty C) f → f = e)
    (v w : Vertex S sort P) (hEdge : CycleEdge C v w) :
    OccurrenceEdge S sort P choice.first v w ∨ OccurrenceEdge S sort P choice.second v w := by
  by_cases hv : v = mark S sort P (left e)
  · subst v
    exact TwoMarkChoices.left_edge_covered S sort P hNonempty C choice w hEdge
  · by_cases hw : w = mark S sort P (left e)
    · subst w
      have hRev := (cycleEdge_symm C _ _).mp hEdge
      rcases TwoMarkChoices.left_edge_covered S sort P hNonempty C choice v hRev with hFirst | hSecond
      · exact Or.inl ((occurrenceEdge_symm S sort P _ _ _).mpr hFirst)
      · exact Or.inr ((occurrenceEdge_symm S sort P _ _ _).mpr hSecond)
    · have hAdj := cycleEdge_adjacent C (Adjacent S sort P)
        (fun v w h => (adjacent_symm S sort P v w).mp h)
        (simpleCycle_adjacent S sort P hNonempty C) hEdge
      obtain ⟨o, p, q, hStep, rfl, rfl⟩ := hAdj
      have hLabel := hAll o.1 (occurrence_label_on_cycle S sort P hNonempty C o p q hStep hEdge)
      have hp0 : p.val ≠ 0 := by
        intro h
        have hp : p = pathStart S (word S sort P o) := Fin.ext h
        rw [hp, at_start, hLabel] at hv
        exact hv rfl
      have hq0 : q.val ≠ 0 := by
        intro h
        have hq : q = pathStart S (word S sort P o) := Fin.ext h
        rw [hq, at_start, hLabel] at hw
        exact hw rfl
      have hOccurrence : o = choice.first ∨ o = choice.second := by
        by_cases hpEnd : p.val = diversityLength S (word S sort P o)
        · have hqEnd : q.val ≠ diversityLength S (word S sort P o) := by
            rcases hStep with h | h <;> omega
          have hOn : CycleVertex C (interior S sort P o ⟨q, hq0, hqEnd⟩) := by
            rw [← at_interior S sort P o ⟨q, hq0, hqEnd⟩]
            exact (cycleEdge_vertices C hEdge).2
          exact TwoMarkChoices.interior_occurrence S sort P hNonempty C choice hAll o ⟨q, hq0, hqEnd⟩ hOn
        · have hOn : CycleVertex C (interior S sort P o ⟨p, hp0, hpEnd⟩) := by
            rw [← at_interior S sort P o ⟨p, hp0, hpEnd⟩]
            exact (cycleEdge_vertices C hEdge).1
          exact TwoMarkChoices.interior_occurrence S sort P hNonempty C choice hAll o ⟨p, hp0, hpEnd⟩ hOn
      rcases hOccurrence with hFirst | hSecond
      · subst o
        exact Or.inl ⟨p, q, hStep, rfl, rfl⟩
      · subst o
        exact Or.inr ⟨p, q, hStep, rfl, rfl⟩

/-- A single used marked edge gives EXACTLY TWO DISTINCT WHOLE original
paths, with equality of literal cycle vertex and traversed-edge supports. -/
theorem cycle_two_whole_paths_of_single_label (e : Edge n)
    (he : CyclicSuppression.LabelOn (initialCycle S sort P hNonempty C) e)
    (hAll : ∀ f, CyclicSuppression.LabelOn (initialCycle S sort P hNonempty C) f → f = e) :
    ∃ first second : Occurrence S sort P,
      first.1 = e ∧ second.1 = e ∧ first ≠ second ∧
      0 < diversityLength S (word S sort P first) ∧
      0 < diversityLength S (word S sort P second) ∧
      (∀ v, CycleVertex C v ↔
        (∃ p, atPosition S sort P first p = v) ∨ (∃ p, atPosition S sort P second p = v)) ∧
      (∀ v w, CycleEdge C v w ↔
        OccurrenceEdge S sort P first v w ∨ OccurrenceEdge S sort P second v w) := by
  obtain ⟨choice⟩ := two_mark_choices S sort P hNonempty C e he hAll
  have hFirstEdge : CycleEdge C (mark S sort P (left choice.first.1))
      (atPosition S sort P choice.first choice.firstPosition) := by
    simpa only [choice.first_label] using choice.first_edge
  have hSecondEdge : CycleEdge C (mark S sort P (left choice.second.1))
      (atPosition S sort P choice.second choice.secondPosition) := by
    simpa only [choice.second_label] using choice.second_edge
  have hFirst := whole_path_on_cycle_of_first_edge S sort P hNonempty C
    choice.first choice.firstPosition choice.first_val hFirstEdge
  have hSecond := whole_path_on_cycle_of_first_edge S sort P hNonempty C
    choice.second choice.secondPosition choice.second_val hSecondEdge
  have hPosFirst : 0 < diversityLength S (word S sort P choice.first) := by
    have h := choice.firstPosition.isLt
    have hval := choice.first_val
    omega
  have hPosSecond : 0 < diversityLength S (word S sort P choice.second) := by
    have h := choice.secondPosition.isLt
    have hval := choice.second_val
    omega
  have hCovered := TwoMarkChoices.cycle_edge_covered S sort P hNonempty C choice hAll
  refine ⟨choice.first, choice.second, choice.first_label, choice.second_label,
    TwoMarkChoices.occurrences_ne S sort P hNonempty C choice, hPosFirst, hPosSecond, ?_, ?_⟩
  · intro v
    constructor
    · intro hOn
      obtain ⟨a, b, _, hA, _⟩ := cycle_two_distinct_neighbours C v hOn
      rcases hCovered v a hA with ⟨p, q, _, hv, _⟩ | ⟨p, q, _, hv, _⟩
      · exact Or.inl ⟨p, hv.symm⟩
      · exact Or.inr ⟨p, hv.symm⟩
    · rintro (⟨p, hp⟩ | ⟨p, hp⟩)
      · rw [← hp]
        exact hFirst.1 p
      · rw [← hp]
        exact hSecond.1 p
  · intro v w
    constructor
    · exact hCovered v w
    · rintro (⟨p, q, hStep, rfl, rfl⟩ | ⟨p, q, hStep, rfl, rfl⟩)
      · exact hFirst.2 p q hStep
      · exact hSecond.2 p q hStep

/-- Full literal source C26 dichotomy. The first alternative retains two
whole original word occurrences, not merely one common underlying label.
The second is a genuine simple marked cyclic embedding preserving all used labels. -/
theorem cycle_two_whole_paths_or_marked_projection :
    (∃ (e : Edge n) (first second : Occurrence S sort P),
      first.1 = e ∧ second.1 = e ∧ first ≠ second ∧
      0 < diversityLength S (word S sort P first) ∧
      0 < diversityLength S (word S sort P second) ∧
      (∀ v, CycleVertex C v ↔
        (∃ p, atPosition S sort P first p = v) ∨ (∃ p, atPosition S sort P second p = v)) ∧
      (∀ v w, CycleEdge C v w ↔
        OccurrenceEdge S sort P first v w ∨ OccurrenceEdge S sort P second v w)) ∨
    Nonempty (MarkedProjection S sort P hNonempty C) := by
  rcases cycle_marked_cases S sort P hNonempty C with hOne | hMany
  · obtain ⟨e, he, _, hAll⟩ := hOne
    obtain ⟨first, second, hf, hs, hne, hp, hq, hVertices, hEdges⟩ :=
      cycle_two_whole_paths_of_single_label S sort P hNonempty C e he hAll
    exact Or.inl ⟨e, first, second, hf, hs, hne, hp, hq, hVertices, hEdges⟩
  · exact Or.inr hMany

end CCO.RawExact.QuotientExpansion
