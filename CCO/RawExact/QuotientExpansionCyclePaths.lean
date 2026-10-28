import CCO.RawExact.QuotientPathExpansion
import CCO.RawExact.SimpleCycleDegreeTwo

/-!
# A raw simple cycle traverses whole private quotient word paths

The finite expansion has no exits at an internal position. Since a
genuine simple cycle has two distinct incident neighbours, both private
path edges must occur on it. Propagating to either end proves that an
occurrence touched in its interior appears as its WHOLE path, including
both actual marked endpoints and every original edge.
-/

universe u v w

namespace CCO.RawExact.QuotientExpansion

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {n : Nat} (sort : Fin n → ι) (P : Menus S sort)
variable {D : PartialDiagram S (Vertex S sort P)}
variable (C : SimpleCycle D)
variable (hCycleAdj : ∀ k, Adjacent S sort P
  (C.vertices k) (C.vertices (cyclicNext C.length_pos k)))

include hCycleAdj

/-- Both ambient path-neighbour edges at an internal cycle vertex
are traversed, not just present in the expanded ambient graph. -/
theorem interior_cycle_neighbor_edge
    (o : Occurrence S sort P) (p : PathPosition S (word S sort P o))
    (hp0 : p.val ≠ 0) (hpEnd : p.val ≠ diversityLength S (word S sort P o))
    (hOn : CycleVertex C (atPosition S sort P o p))
    (q : PathPosition S (word S sort P o))
    (hpq : pathAdjacent S (word S sort P o) p q) :
    CycleEdge C (atPosition S sort P o p) (atPosition S sort P o q) := by
  have hpBound := p.isLt
  obtain ⟨before, after, hBefore, hAfter, _, _, _, hExhaustPath⟩ :=
    pathInterior_exactly_two_neighbours S (word S sort P o) p (by omega) (by omega)
  let pp : Interior S sort P o := ⟨p, hp0, hpEnd⟩
  have hOnPrivate : CycleVertex C (interior S sort P o pp) := by
    rw [← at_interior S sort P o pp]
    exact hOn
  have hExhaust : ∀ v, Adjacent S sort P (interior S sort P o pp) v →
      v = atPosition S sort P o before ∨ v = atPosition S sort P o after := by
    intro v hv
    obtain ⟨r, hpr, rfl⟩ := (adjacent_interior_iff S sort P o pp v).mp hv
    rcases hExhaustPath r hpr with hr | hr
    · exact Or.inl (congrArg (atPosition S sort P o) hr)
    · exact Or.inr (congrArg (atPosition S sort P o) hr)
  have hEdges := cycle_degree_two_edges C (Adjacent S sort P)
    (fun v w h => (adjacent_symm S sort P v w).mp h) hCycleAdj
    (interior S sort P o pp) (atPosition S sort P o before)
    (atPosition S sort P o after) hExhaust hOnPrivate
  rw [← at_interior S sort P o pp] at hEdges
  rcases hExhaustPath q hpq with hq | hq
  · simpa only [hq] using hEdges.1
  · simpa only [hq] using hEdges.2

/-- Touching ONE private interior forces EVERY position of that
word occurrence, and all its edges, into the same actual simple cycle. -/
theorem whole_path_on_cycle_of_interior
    (o : Occurrence S sort P) (p : Interior S sort P o)
    (hOn : CycleVertex C (interior S sort P o p)) :
    (∀ q : PathPosition S (word S sort P o),
      CycleVertex C (atPosition S sort P o q)) ∧
    (∀ q r : PathPosition S (word S sort P o),
      pathAdjacent S (word S sort P o) q r →
        CycleEdge C (atPosition S sort P o q) (atPosition S sort P o r)) := by
  have hpBound := p.1.isLt
  have hp0 := p.property.1
  have hpEnd := p.property.2
  have hpStart : 0 < p.1.val := by omega
  have hpFinish : p.1.val < diversityLength S (word S sort P o) := by omega
  have hAtP : CycleVertex C (atPosition S sort P o p.1) := by
    rw [at_interior S sort P o p]
    exact hOn
  have hDown : ∀ d : Nat, ∀ hd : d ≤ p.1.val,
      CycleVertex C (atPosition S sort P o
        ⟨p.1.val - d, by omega⟩) := by
    intro d
    induction d with
    | zero =>
        intro hd
        simpa only [Nat.sub_zero] using hAtP
    | succ d ih =>
        intro hd
        have hdPrev : d ≤ p.1.val := by omega
        let current : PathPosition S (word S sort P o) := ⟨p.1.val - d, by omega⟩
        let next : PathPosition S (word S sort P o) := ⟨p.1.val - (d + 1), by omega⟩
        have hCurrent : CycleVertex C (atPosition S sort P o current) := ih hdPrev
        have hEdge := interior_cycle_neighbor_edge S sort P C hCycleAdj o current
          (by dsimp [current]; omega) (by dsimp [current]; omega) hCurrent next
          (Or.inr (by dsimp [current, next]; omega))
        exact (cycleEdge_vertices C hEdge).2
  have hUp : ∀ d : Nat, ∀ hd : p.1.val + d ≤ diversityLength S (word S sort P o),
      CycleVertex C (atPosition S sort P o
        ⟨p.1.val + d, by omega⟩) := by
    intro d
    induction d with
    | zero =>
        intro hd
        simpa only [Nat.add_zero] using hAtP
    | succ d ih =>
        intro hd
        have hdPrev : p.1.val + d ≤ diversityLength S (word S sort P o) := by omega
        let current : PathPosition S (word S sort P o) := ⟨p.1.val + d, by omega⟩
        let next : PathPosition S (word S sort P o) := ⟨p.1.val + (d + 1), by omega⟩
        have hCurrent : CycleVertex C (atPosition S sort P o current) := ih hdPrev
        have hEdge := interior_cycle_neighbor_edge S sort P C hCycleAdj o current
          (by dsimp [current]; omega) (by dsimp [current]; omega) hCurrent next
          (Or.inl (by dsimp [current, next]; omega))
        exact (cycleEdge_vertices C hEdge).2
  have hAll : ∀ q : PathPosition S (word S sort P o),
      CycleVertex C (atPosition S sort P o q) := by
    intro q
    have hqBound := q.isLt
    by_cases hqp : q.val ≤ p.1.val
    · have hd : p.1.val - q.val ≤ p.1.val := by omega
      have h := hDown (p.1.val - q.val) hd
      let r : PathPosition S (word S sort P o) := ⟨p.1.val - (p.1.val - q.val), by omega⟩
      change CycleVertex C (atPosition S sort P o r) at h
      have hrq : r = q := Fin.ext (by dsimp [r]; omega)
      simpa only [hrq] using h
    · have hd : p.1.val + (q.val - p.1.val) ≤ diversityLength S (word S sort P o) := by omega
      have h := hUp (q.val - p.1.val) hd
      let r : PathPosition S (word S sort P o) := ⟨p.1.val + (q.val - p.1.val), by omega⟩
      change CycleVertex C (atPosition S sort P o r) at h
      have hrq : r = q := Fin.ext (by dsimp [r]; omega)
      simpa only [hrq] using h
  refine ⟨hAll, ?_⟩
  intro q r hqr
  have hqBound := q.isLt
  have hrBound := r.isLt
  by_cases hq0 : q.val = 0
  · have hr0 : r.val ≠ 0 := by rcases hqr with h | h <;> omega
    have hrEnd : r.val ≠ diversityLength S (word S sort P o) := by
      rcases hqr with h | h <;> omega
    apply (cycleEdge_symm C _ _).mpr
    exact interior_cycle_neighbor_edge S sort P C hCycleAdj o r hr0 hrEnd (hAll r) q
      ((pathAdjacent_symm S _ q r).mp hqr)
  · by_cases hqEnd : q.val = diversityLength S (word S sort P o)
    · have hr0 : r.val ≠ 0 := by rcases hqr with h | h <;> omega
      have hrEnd : r.val ≠ diversityLength S (word S sort P o) := by
        rcases hqr with h | h <;> omega
      apply (cycleEdge_symm C _ _).mpr
      exact interior_cycle_neighbor_edge S sort P C hCycleAdj o r hr0 hrEnd (hAll r) q
        ((pathAdjacent_symm S _ q r).mp hqr)
    · exact interior_cycle_neighbor_edge S sort P C hCycleAdj o q hq0 hqEnd (hAll q) r hqr

end CCO.RawExact.QuotientExpansion
