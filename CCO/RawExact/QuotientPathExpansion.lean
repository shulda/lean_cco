import CCO.RawExact.PathEndpoints
import CCO.RawExact.PathLocalDegree
import Mathlib.Basic.Finite.Prod
import Mathlib.Basic.Finite.Sigma
import Mathlib.Basic.Finite.Sum

/-!
# Private word-path expansion of a finite marked diagram

Every unordered marked pair has one canonical orientation. Every listed
word keeps its own private internal positions; only its two endpoints
are shared marked vertices. Empty menus introduce no paths. Logical
identity letters contribute no edge. Source positivity and actual edge
colour compatibility are discharged separately before CCO is applied.
-/

universe u v w

namespace CCO.RawExact.QuotientExpansion

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)

/-- Canonically oriented unordered pairs of DISTINCT marked vertices. -/
abbrev Edge (n : Nat) := {e : Fin n × Fin n // e.1 < e.2}

def left {n : Nat} (e : Edge n) : Fin n := e.val.1
def right {n : Nat} (e : Edge n) : Fin n := e.val.2

theorem left_ne_right {n : Nat} (e : Edge n) : left e ≠ right e :=
  ne_of_lt e.property

variable {n : Nat} (sort : Fin n → ι)

/-- One finite typed word menu per unoriented marked pair. A missing
constraint may be assigned the empty menu (represented typed Top). -/
abbrev Menus := ∀ e : Edge n, Presentation S (sort (left e)) (sort (right e))

abbrev Occurrence (P : Menus S sort) := Σ e : Edge n, Fin (P e).length

def word (P : Menus S sort) (o : Occurrence S sort P) :
    RawWord S (sort (left o.1)) (sort (right o.1)) :=
  (P o.1).get o.2

abbrev Interior (P : Menus S sort) (o : Occurrence S sort P) :=
  {p : PathPosition S (word S sort P o) //
    p.val ≠ 0 ∧ p.val ≠ diversityLength S (word S sort P o)}

/-- All marked vertices, plus one fresh vertex at each strict interior
position of every word occurrence of every marked edge. -/
abbrev Vertex (P : Menus S sort) :=
  Fin n ⊕ (Σ o : Occurrence S sort P, Interior S sort P o)

instance vertex_finite (P : Menus S sort) : Finite (Vertex S sort P) := by
  unfold Vertex Interior Occurrence Edge
  infer_instance

def mark (P : Menus S sort) (v : Fin n) : Vertex S sort P := .inl v

def interior (P : Menus S sort) (o : Occurrence S sort P)
    (p : Interior S sort P o) : Vertex S sort P := .inr ⟨o, p⟩

def atPosition (P : Menus S sort) (o : Occurrence S sort P)
    (p : PathPosition S (word S sort P o)) : Vertex S sort P :=
  if h0 : p.val = 0 then mark S sort P (left o.1)
  else if hEnd : p.val = diversityLength S (word S sort P o) then
    mark S sort P (right o.1)
  else interior S sort P o ⟨p, h0, hEnd⟩

def vertexSort (P : Menus S sort) : Vertex S sort P → ι
  | .inl v => sort v
  | .inr ⟨o, p⟩ => pathSortAt S (word S sort P o) p.1

theorem at_start (P : Menus S sort) (o : Occurrence S sort P) :
    atPosition S sort P o (pathStart S (word S sort P o)) = mark S sort P (left o.1) := by
  simp [atPosition, pathStart]

theorem at_finish (P : Menus S sort) (o : Occurrence S sort P)
    (hPos : 0 < diversityLength S (word S sort P o)) :
    atPosition S sort P o (pathFinish S (word S sort P o)) = mark S sort P (right o.1) := by
  simp [atPosition, pathFinish, Nat.ne_of_gt hPos]

theorem at_interior (P : Menus S sort) (o : Occurrence S sort P)
    (p : Interior S sort P o) :
    atPosition S sort P o p.1 = interior S sort P o p := by
  simp [atPosition, p.property.1, p.property.2]

theorem at_injective (P : Menus S sort) (o : Occurrence S sort P) :
    Function.Injective (atPosition S sort P o) := by
  intro p q hpq
  have hEnds := left_ne_right o.1
  have hVal : p.val = q.val := by
    by_cases hp0 : p.val = 0 <;>
    by_cases hpEnd : p.val = diversityLength S (word S sort P o) <;>
    by_cases hq0 : q.val = 0 <;>
    by_cases hqEnd : q.val = diversityLength S (word S sort P o) <;>
      simp_all [atPosition, mark, interior]
  exact Fin.ext hVal

/-- Every formal path position has its genuine ORIGINAL named sort. -/
theorem at_sort (P : Menus S sort) (o : Occurrence S sort P)
    (p : PathPosition S (word S sort P o)) :
    vertexSort S sort P (atPosition S sort P o p) = pathSortAt S (word S sort P o) p := by
  by_cases hp0 : p.val = 0
  · have hp : p = pathStart S (word S sort P o) := Fin.ext hp0
    rw [hp, at_start]
    exact (pathSortAt_start S (word S sort P o)).symm
  · by_cases hpEnd : p.val = diversityLength S (word S sort P o)
    · have hp : p = pathFinish S (word S sort P o) := Fin.ext hpEnd
      rw [hp, at_finish S sort P o (by omega)]
      exact (pathSortAt_finish S (word S sort P o)).symm
    · rw [show atPosition S sort P o p = interior S sort P o ⟨p, hp0, hpEnd⟩ by
        simp [atPosition, hp0, hpEnd]]
      rfl

/-- The expansion graph contains exactly genuine private-word edges;
there are no extra centre-clique edges in a quotient diagram expansion. -/
def Adjacent (P : Menus S sort) (v w : Vertex S sort P) : Prop :=
  ∃ (o : Occurrence S sort P) (p q : PathPosition S (word S sort P o)),
    pathAdjacent S (word S sort P o) p q ∧ v = atPosition S sort P o p ∧ w = atPosition S sort P o q

theorem adjacent_symm (P : Menus S sort) (v w : Vertex S sort P) :
    Adjacent S sort P v w ↔ Adjacent S sort P w v := by
  constructor <;> rintro ⟨o, p, q, hpq, hv, hw⟩
  · exact ⟨o, q, p, (pathAdjacent_symm S _ p q).mp hpq, hw, hv⟩
  · exact ⟨o, q, p, (pathAdjacent_symm S _ p q).mp hpq, hw, hv⟩

theorem adjacent_irrefl (P : Menus S sort) (v : Vertex S sort P) :
    ¬ Adjacent S sort P v v := by
  rintro ⟨o, p, q, hpq, hv, hw⟩
  have heq := at_injective S sort P o (hv.symm.trans hw)
  subst q
  exact pathAdjacent_irrefl S _ p hpq

/-- A private interior belongs to exactly its own word occurrence. -/
theorem interior_occurrence_unique (P : Menus S sort)
    (o o' : Occurrence S sort P) (p : Interior S sort P o)
    (q : PathPosition S (word S sort P o'))
    (h : interior S sort P o p = atPosition S sort P o' q) : o = o' := by
  unfold atPosition at h
  split_ifs at h with hq0 hqEnd
  · cases h
  · cases h
  · exact (Sigma.mk.inj (Sum.inr.inj h)).1

/-- No graph edge can leave a private path at an internal vertex. -/
theorem adjacent_interior_iff (P : Menus S sort)
    (o : Occurrence S sort P) (p : Interior S sort P o)
    (v : Vertex S sort P) :
    Adjacent S sort P (interior S sort P o p) v ↔
      ∃ q : PathPosition S (word S sort P o),
        pathAdjacent S (word S sort P o) p.1 q ∧ v = atPosition S sort P o q := by
  constructor
  · rintro ⟨o', q, r, hqr, hq, hr⟩
    have hoo' := interior_occurrence_unique S sort P o o' p q hq
    subst o'
    have hpq : p.1 = q :=
      at_injective S sort P o ((at_interior S sort P o p).trans hq)
    subst q
    exact ⟨r, hqr, hr⟩
  · rintro ⟨q, hpq, hv⟩
    exact ⟨o, p.1, q, hpq, (at_interior S sort P o p).symm, hv⟩

end CCO.RawExact.QuotientExpansion
