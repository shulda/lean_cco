import CCO.RawExact.QuotientExpansionCycleCases

/-!
# Literal branch germs in a two-mark private expansion cycle

The two actual neighbours of the left marked endpoint choose two whole
original word occurrences. Direct duplicate words still give only one
formal graph edge and cannot supply both cycle incidences.
-/

universe u v w
namespace CCO.RawExact.QuotientExpansion
variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {n : Nat} (sort : Fin n → ι) (P : Menus S sort)
variable (hNonempty : ∀ e, TRel.Nonempty (evaluate S (P e)))
variable (C : SimpleCycle (diagram S sort P hNonempty))

/-- One literal edge of one named private word occurrence. -/
def OccurrenceEdge (o : Occurrence S sort P) (v w : Vertex S sort P) : Prop :=
  ∃ p q : PathPosition S (word S sort P o),
    pathAdjacent S (word S sort P o) p q ∧
      v = atPosition S sort P o p ∧ w = atPosition S sort P o q

theorem occurrenceEdge_symm (o : Occurrence S sort P) (v w : Vertex S sort P) :
    OccurrenceEdge S sort P o v w ↔ OccurrenceEdge S sort P o w v := by
  constructor <;> rintro ⟨p, q, hpq, hv, hw⟩
  · exact ⟨q, p, (pathAdjacent_symm S _ p q).mp hpq, hw, hv⟩
  · exact ⟨q, p, (pathAdjacent_symm S _ p q).mp hpq, hw, hv⟩

/-- A traversed edge of an explicitly named path uses its actual marked label. -/
theorem occurrence_label_on_cycle
    (o : Occurrence S sort P) (p q : PathPosition S (word S sort P o))
    (hpq : pathAdjacent S (word S sort P o) p q)
    (hEdge : CycleEdge C (atPosition S sort P o p) (atPosition S sort P o q)) :
    CyclicSuppression.LabelOn (initialCycle S sort P hNonempty C) o.1 := by
  obtain ⟨k, h | h⟩ := hEdge
  · exact ⟨k, initial_label_of_path_witness S sort P hNonempty C k o p q hpq h.1 h.2⟩
  · exact ⟨k, initial_label_of_path_witness S sort P hNonempty C k o q p
      ((pathAdjacent_symm S _ p q).mp hpq) h.1 h.2⟩

/-- The actual incoming and outgoing cycle edges exhaust incidence at a mark. -/
theorem cycle_mark_neighbours (m : Fin n) (hOn : CycleVertex C (mark S sort P m)) :
    ∃ a b : Vertex S sort P, a ≠ b ∧
      CycleEdge C (mark S sort P m) a ∧ CycleEdge C (mark S sort P m) b ∧
      ∀ v, CycleEdge C (mark S sort P m) v → v = a ∨ v = b := by
  obtain ⟨p, hp⟩ := hOn
  obtain ⟨prev, hprev, hUnique, hPrevUnique⟩ := cycle_root_incidences C (mark S sort P m) p hp
  refine ⟨C.vertices prev, C.vertices (cyclicNext C.length_pos p), ?_, ?_, ?_, ?_⟩
  · intro h
    have hIndex := C.vertices.injective h
    exact cyclicNext_no_two_cycle C.length_pos C.length_ge_three p prev hIndex.symm hprev
  · exact ⟨prev, Or.inr ⟨rfl, (congrArg C.vertices hprev).trans hp⟩⟩
  · exact ⟨p, Or.inl ⟨hp, rfl⟩⟩
  · intro v hv
    obtain ⟨q, h | h⟩ := hv
    · have hq := hUnique q h.1
      subst q
      exact Or.inr h.2.symm
    · have hq := hPrevUnique q h.2
      subst q
      exact Or.inl h.1.symm

/-- Under the proved single-label alternative, every left marked cycle
edge is the first step of one actual occurrence of precisely that edge. -/
theorem single_label_left_edge_first_step
    (e : Edge n)
    (hAll : ∀ f, CyclicSuppression.LabelOn (initialCycle S sort P hNonempty C) f → f = e)
    (v : Vertex S sort P) (hEdge : CycleEdge C (mark S sort P (left e)) v) :
    ∃ (o : Occurrence S sort P) (q : PathPosition S (word S sort P o)),
      o.1 = e ∧ q.val = 1 ∧ v = atPosition S sort P o q := by
  have hAdj := cycleEdge_adjacent C (Adjacent S sort P)
    (fun v w h => (adjacent_symm S sort P v w).mp h)
    (simpleCycle_adjacent S sort P hNonempty C) hEdge
  obtain ⟨o, p, q, hpq, hp, hv⟩ := hAdj
  have hLabel : o.1 = e := hAll o.1 (occurrence_label_on_cycle S sort P hNonempty C o p q hpq
    (by simpa only [← hp, ← hv] using hEdge))
  have hPos : p.val = 0 := by
    rcases mark_position_endpoint S sort P o p (left e) hp with h | h
    · exact h.1
    · have hBad : left e = right e := by simpa only [hLabel] using h.2
      exact False.elim (left_ne_right e hBad)
  refine ⟨o, q, hLabel, ?_, hv⟩
  rcases hpq with h | h <;> omega

/-- A selected first edge forces its WHOLE occurrence, including direct words. -/
theorem whole_path_on_cycle_of_first_edge
    (o : Occurrence S sort P) (q : PathPosition S (word S sort P o)) (hq : q.val = 1)
    (hEdge : CycleEdge C (mark S sort P (left o.1)) (atPosition S sort P o q)) :
    (∀ r : PathPosition S (word S sort P o), CycleVertex C (atPosition S sort P o r)) ∧
    (∀ r s : PathPosition S (word S sort P o), pathAdjacent S (word S sort P o) r s →
      CycleEdge C (atPosition S sort P o r) (atPosition S sort P o s)) := by
  have hqBound := q.isLt
  by_cases hEnd : q.val = diversityLength S (word S sort P o)
  · have hLen : diversityLength S (word S sort P o) = 1 := by omega
    constructor
    · intro r
      have hrBound := r.isLt
      by_cases hr0 : r.val = 0
      · have hr : r = pathStart S (word S sort P o) := Fin.ext hr0
        rw [hr, at_start]
        exact (cycleEdge_vertices C hEdge).1
      · have hr : r = q := Fin.ext (by omega)
        rw [hr]
        exact (cycleEdge_vertices C hEdge).2
    · intro r s hStep
      have hrBound := r.isLt
      have hsBound := s.isLt
      by_cases hr0 : r.val = 0
      · have hr : r = pathStart S (word S sort P o) := Fin.ext hr0
        have hs : s = q := Fin.ext (by rcases hStep with h | h <;> omega)
        rw [hr, hs, at_start]
        exact hEdge
      · have hr : r = q := Fin.ext (by omega)
        have hs : s = pathStart S (word S sort P o) :=
          Fin.ext (by change s.val = 0; rcases hStep with h | h <;> omega)
        rw [hr, hs, at_start]
        exact (cycleEdge_symm C _ _).mp hEdge
  · have hq0 : q.val ≠ 0 := by omega
    let p : Interior S sort P o := ⟨q, hq0, hEnd⟩
    have hOn : CycleVertex C (interior S sort P o p) := by
      rw [← at_interior S sort P o p]
      exact (cycleEdge_vertices C hEdge).2
    exact whole_path_on_cycle_of_interior S sort P C (simpleCycle_adjacent S sort P hNonempty C) o p hOn

end CCO.RawExact.QuotientExpansion
