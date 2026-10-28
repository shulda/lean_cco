import CCO.RawExact.WordThetaCycleClassificationIncidence

/-!
# Complete private branches selected by literal theta root edges

A length-one branch is the one merged root--centre graph edge. A longer
branch is forced in full by its first private interior and degree two.
All conclusions concern edges actually traversed by the same simple cycle.
-/

universe u v w
namespace CCO.RawExact
variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {root : ι} {I : Type (max u v)} [Finite I] {sort : I → ι}
variable (menus : ∀ t : I, NonemptyExact S root (sort t)) (centres : ∀ t : I, X (sort t))
variable {E : PartialDiagram S (PrivateFanVertex S menus centres)} (C : SimpleCycle E)
variable (hCycleAdj : ∀ k, privateFanAdjacent S menus centres
  (C.vertices k) (C.vertices (cyclicNext C.length_pos k)))

/-- An edge of ONE named private occurrence, with orientation retained in its endpoints. -/
def PrivateOccurrenceEdge (o : WordOccurrence S menus) (v w : PrivateFanVertex S menus centres) : Prop :=
  ∃ p q : PathPosition S (occurrenceWord S menus o),
    pathAdjacent S (occurrenceWord S menus o) p q ∧
      v = privateFanAtWordPosition S menus centres o p ∧
      w = privateFanAtWordPosition S menus centres o q

include hCycleAdj

/-- Any selected first edge forces its entire positive private branch,
including a genuine length-one merged direct branch. -/
theorem privateFan_whole_path_on_cycle_of_root_edge
    (o : WordOccurrence S menus) (q : PathPosition S (occurrenceWord S menus o)) (hq : q.val = 1)
    (hEdge : CycleEdge C (privateFanRoot S menus centres) (privateFanAtWordPosition S menus centres o q)) :
    (∀ r : PathPosition S (occurrenceWord S menus o),
      CycleVertex C (privateFanAtWordPosition S menus centres o r)) ∧
    (∀ r s : PathPosition S (occurrenceWord S menus o),
      pathAdjacent S (occurrenceWord S menus o) r s →
        CycleEdge C (privateFanAtWordPosition S menus centres o r) (privateFanAtWordPosition S menus centres o s)) := by
  have hqBound := q.isLt
  by_cases hEnd : q.val = diversityLength S (occurrenceWord S menus o)
  · have hLen : diversityLength S (occurrenceWord S menus o) = 1 := by omega
    constructor
    · intro r
      have hrBound := r.isLt
      by_cases hr0 : r.val = 0
      · have hr : r = pathStart S (occurrenceWord S menus o) := Fin.ext hr0
        rw [hr, privateFanAt_start S menus centres o]
        exact (cycleEdge_vertices C hEdge).1
      · have hr : r = q := Fin.ext (by omega)
        rw [hr]
        exact (cycleEdge_vertices C hEdge).2
    · intro r s hStep
      have hrBound := r.isLt
      have hsBound := s.isLt
      by_cases hr0 : r.val = 0
      · have hr : r = pathStart S (occurrenceWord S menus o) := Fin.ext hr0
        have hs : s = q := Fin.ext (by rcases hStep with h | h <;> omega)
        rw [hr, hs, privateFanAt_start S menus centres o]
        exact hEdge
      · have hr : r = q := Fin.ext (by omega)
        have hs : s = pathStart S (occurrenceWord S menus o) :=
          Fin.ext (by change s.val = 0; rcases hStep with h | h <;> omega)
        rw [hr, hs, privateFanAt_start S menus centres o]
        exact (cycleEdge_symm C _ _).mp hEdge
  · have hq0 : q.val ≠ 0 := by omega
    let p : PrivateInteriorPosition S menus o := ⟨q, hq0, hEnd⟩
    have hOn : CycleVertex C (privateFanInterior S menus centres o p) := by
      rw [← privateFanAt_interior S menus centres o q hq0 hEnd]
      exact (cycleEdge_vertices C hEdge).2
    exact privateFan_whole_path_on_cycle_of_interior S menus centres C hCycleAdj o p hOn

end CCO.RawExact
