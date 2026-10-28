import CCO.RawExact.FanTerminalIncidence
import CCO.RawExact.SimpleCycleDegreeTwo

/-!
# C06: a RAW theta cycle traverses complete private word paths

The actual private fan has no exits at an internal position. Since a
genuine simple cycle has two distinct incident neighbours, both private
path edges must occur on it. Propagating to either end proves that an
occurrence touched in its interior appears as its WHOLE path, including
both actual marked endpoints and every original edge.
-/

universe u v w

namespace CCO.RawExact

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {root : ι} {I : Type (max u v)} [Finite I] {sort : I → ι}
variable (menus : ∀ t : I, NonemptyExact S root (sort t)) (centres : ∀ t : I, X (sort t))
variable {E : PartialDiagram S (PrivateFanVertex S menus centres)}
variable (C : SimpleCycle E)
variable (hCycleAdj : ∀ k, privateFanAdjacent S menus centres
  (C.vertices k) (C.vertices (cyclicNext C.length_pos k)))

include hCycleAdj

/-- Both ambient path-neighbour edges at an internal cycle vertex
are traversed, not just present in the expanded ambient graph. -/
theorem privateFanInterior_cycle_neighbor_edge
    (o : WordOccurrence S menus) (p : PathPosition S (occurrenceWord S menus o))
    (hp0 : p.val ≠ 0) (hpEnd : p.val ≠ diversityLength S (occurrenceWord S menus o))
    (hOn : CycleVertex C (privateFanAtWordPosition S menus centres o p))
    (q : PathPosition S (occurrenceWord S menus o))
    (hpq : pathAdjacent S (occurrenceWord S menus o) p q) :
    CycleEdge C (privateFanAtWordPosition S menus centres o p) (privateFanAtWordPosition S menus centres o q) := by
  have hpBound := p.isLt
  obtain ⟨before, after, hBefore, hAfter, _, _, _, hExhaustPath⟩ :=
    pathInterior_exactly_two_neighbours S (occurrenceWord S menus o) p (by omega) (by omega)
  let pp : PrivateInteriorPosition S menus o := ⟨p, hp0, hpEnd⟩
  have hOnPrivate : CycleVertex C (privateFanInterior S menus centres o pp) := by
    rw [← privateFanAt_interior S menus centres o pp.1 pp.property.1 pp.property.2]
    exact hOn
  have hExhaust : ∀ v, privateFanAdjacent S menus centres (privateFanInterior S menus centres o pp) v →
      v = privateFanAtWordPosition S menus centres o before ∨ v = privateFanAtWordPosition S menus centres o after := by
    intro v hv
    obtain ⟨r, hpr, rfl⟩ := privateFanInterior_neighbours_only_own_path S menus centres o pp v hv
    rcases hExhaustPath r hpr with hr | hr
    · exact Or.inl (congrArg (privateFanAtWordPosition S menus centres o) hr)
    · exact Or.inr (congrArg (privateFanAtWordPosition S menus centres o) hr)
  have hEdges := cycle_degree_two_edges C (privateFanAdjacent S menus centres)
    (fun v w h => (privateFanAdjacent_symm S menus centres v w).mp h) hCycleAdj
    (privateFanInterior S menus centres o pp) (privateFanAtWordPosition S menus centres o before)
    (privateFanAtWordPosition S menus centres o after) hExhaust hOnPrivate
  rw [← privateFanAt_interior S menus centres o pp.1 pp.property.1 pp.property.2] at hEdges
  rcases hExhaustPath q hpq with hq | hq
  · simpa only [hq] using hEdges.1
  · simpa only [hq] using hEdges.2

/-- Touching ONE private interior forces EVERY position of that
word occurrence, and all its edges, into the same actual simple cycle. -/
theorem privateFan_whole_path_on_cycle_of_interior
    (o : WordOccurrence S menus) (p : PrivateInteriorPosition S menus o)
    (hOn : CycleVertex C (privateFanInterior S menus centres o p)) :
    (∀ q : PathPosition S (occurrenceWord S menus o),
      CycleVertex C (privateFanAtWordPosition S menus centres o q)) ∧
    (∀ q r : PathPosition S (occurrenceWord S menus o),
      pathAdjacent S (occurrenceWord S menus o) q r →
        CycleEdge C (privateFanAtWordPosition S menus centres o q) (privateFanAtWordPosition S menus centres o r)) := by
  have hpBound := p.1.isLt
  have hp0 := p.property.1
  have hpEnd := p.property.2
  have hpStart : 0 < p.1.val := by omega
  have hpFinish : p.1.val < diversityLength S (occurrenceWord S menus o) := by omega
  have hAtP : CycleVertex C (privateFanAtWordPosition S menus centres o p.1) := by
    rw [privateFanAt_interior S menus centres o p.1 p.property.1 p.property.2]
    exact hOn
  have hDown : ∀ d : Nat, ∀ hd : d ≤ p.1.val,
      CycleVertex C (privateFanAtWordPosition S menus centres o
        ⟨p.1.val - d, by omega⟩) := by
    intro d
    induction d with
    | zero =>
        intro hd
        simpa only [Nat.sub_zero] using hAtP
    | succ d ih =>
        intro hd
        have hdPrev : d ≤ p.1.val := by omega
        let current : PathPosition S (occurrenceWord S menus o) := ⟨p.1.val - d, by omega⟩
        let next : PathPosition S (occurrenceWord S menus o) := ⟨p.1.val - (d + 1), by omega⟩
        have hCurrent : CycleVertex C (privateFanAtWordPosition S menus centres o current) := ih hdPrev
        have hEdge := privateFanInterior_cycle_neighbor_edge S menus centres C hCycleAdj o current
          (by dsimp [current]; omega) (by dsimp [current]; omega) hCurrent next
          (Or.inr (by dsimp [current, next]; omega))
        exact (cycleEdge_vertices C hEdge).2
  have hUp : ∀ d : Nat, ∀ hd : p.1.val + d ≤ diversityLength S (occurrenceWord S menus o),
      CycleVertex C (privateFanAtWordPosition S menus centres o
        ⟨p.1.val + d, by omega⟩) := by
    intro d
    induction d with
    | zero =>
        intro hd
        simpa only [Nat.add_zero] using hAtP
    | succ d ih =>
        intro hd
        have hdPrev : p.1.val + d ≤ diversityLength S (occurrenceWord S menus o) := by omega
        let current : PathPosition S (occurrenceWord S menus o) := ⟨p.1.val + d, by omega⟩
        let next : PathPosition S (occurrenceWord S menus o) := ⟨p.1.val + (d + 1), by omega⟩
        have hCurrent : CycleVertex C (privateFanAtWordPosition S menus centres o current) := ih hdPrev
        have hEdge := privateFanInterior_cycle_neighbor_edge S menus centres C hCycleAdj o current
          (by dsimp [current]; omega) (by dsimp [current]; omega) hCurrent next
          (Or.inl (by dsimp [current, next]; omega))
        exact (cycleEdge_vertices C hEdge).2
  have hAll : ∀ q : PathPosition S (occurrenceWord S menus o),
      CycleVertex C (privateFanAtWordPosition S menus centres o q) := by
    intro q
    have hqBound := q.isLt
    by_cases hqp : q.val ≤ p.1.val
    · have hd : p.1.val - q.val ≤ p.1.val := by omega
      have h := hDown (p.1.val - q.val) hd
      let r : PathPosition S (occurrenceWord S menus o) := ⟨p.1.val - (p.1.val - q.val), by omega⟩
      change CycleVertex C (privateFanAtWordPosition S menus centres o r) at h
      have hrq : r = q := Fin.ext (by dsimp [r]; omega)
      simpa only [hrq] using h
    · have hd : p.1.val + (q.val - p.1.val) ≤ diversityLength S (occurrenceWord S menus o) := by omega
      have h := hUp (q.val - p.1.val) hd
      let r : PathPosition S (occurrenceWord S menus o) := ⟨p.1.val + (q.val - p.1.val), by omega⟩
      change CycleVertex C (privateFanAtWordPosition S menus centres o r) at h
      have hrq : r = q := Fin.ext (by dsimp [r]; omega)
      simpa only [hrq] using h
  refine ⟨hAll, ?_⟩
  intro q r hqr
  have hqBound := q.isLt
  have hrBound := r.isLt
  by_cases hq0 : q.val = 0
  · have hr0 : r.val ≠ 0 := by rcases hqr with h | h <;> omega
    have hrEnd : r.val ≠ diversityLength S (occurrenceWord S menus o) := by
      rcases hqr with h | h <;> omega
    apply (cycleEdge_symm C _ _).mpr
    exact privateFanInterior_cycle_neighbor_edge S menus centres C hCycleAdj o r hr0 hrEnd (hAll r) q
      ((pathAdjacent_symm S _ q r).mp hqr)
  · by_cases hqEnd : q.val = diversityLength S (occurrenceWord S menus o)
    · have hr0 : r.val ≠ 0 := by rcases hqr with h | h <;> omega
      have hrEnd : r.val ≠ diversityLength S (occurrenceWord S menus o) := by
        rcases hqr with h | h <;> omega
      apply (cycleEdge_symm C _ _).mpr
      exact privateFanInterior_cycle_neighbor_edge S menus centres C hCycleAdj o r hr0 hrEnd (hAll r) q
        ((pathAdjacent_symm S _ q r).mp hqr)
    · exact privateFanInterior_cycle_neighbor_edge S menus centres C hCycleAdj o q hq0 hqEnd (hAll q) r hqr

end CCO.RawExact
