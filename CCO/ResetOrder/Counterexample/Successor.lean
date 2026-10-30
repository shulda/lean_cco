import CCO.ResetOrder.Counterexample.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.EquivFin

/-! The added unary function is the actual next point of the ordered P-class,
fixing its maximum. Its existence and uniqueness are proved for every finite
ordered nested-equivalence structure. -/
universe u v
namespace CCO.ResetOrder.Counterexample.Nested.ConvexOrder
variable {X : Type u} {Y : Type v} {A : Nested X} {B : Nested Y}

structure Successor (a : ConvexOrder A) where
  next : X → X
  sameP : ∀ x, A.P.r x (next x)
  le_next : ∀ x, a.order.le x (next x)
  least : ∀ x y, A.P.r x y → a.order.lt x y → a.order.le (next x) y
  strict : ∀ x, (∃ y, A.P.r x y ∧ a.order.lt x y) → a.order.lt x (next x)

namespace Successor
variable {a : ConvexOrder A} {b : ConvexOrder B}

theorem fixed_iff (s : Successor a) (x : X) :
    s.next x = x ↔ ∀ y, A.P.r x y → a.order.le y x := by
  letI := a.order
  constructor
  · intro hx y hP
    by_contra! h
    have := s.strict x ⟨y, hP, h⟩
    simpa only [hx, lt_self_iff_false] using this
  · intro h
    exact le_antisymm (h _ (s.sameP x)) (s.le_next x)

theorem no_between (s : Successor a) {x y : X} (hP : A.P.r x y)
    (hxy : a.order.lt x y) : ¬ a.order.lt y (s.next x) := by
  letI := a.order
  exact not_lt_of_ge (s.least x y hP hxy)

@[ext] theorem ext {s t : Successor a} (h : ∀ x, s.next x = t.next x) : s = t := by
  cases s with
  | mk sp sP sle smin sstrict =>
    cases t with
    | mk tp tP tle tmin tstrict =>
      have hp : sp = tp := funext h
      subst tp
      rfl

theorem unique (s t : Successor a) : s = t := by
  letI := a.order
  apply ext
  intro x
  by_cases h : ∃ y, A.P.r x y ∧ x < y
  · exact le_antisymm (s.least x _ (t.sameP x) (t.strict x h))
      (t.least x _ (s.sameP x) (s.strict x h))
  · have hx : ∀ y, A.P.r x y → y ≤ x := by
      intro y hy
      exact le_of_not_gt (fun hxy => h ⟨y, hy, hxy⟩)
    rw [(s.fixed_iff x).2 hx, (t.fixed_iff x).2 hx]

/-- The complete induced-map condition includes preservation of the added
function, in addition to both equivalences and the order. -/
structure Embedding (s : Successor a) (t : Successor b) extends toOrderedEmbedding : ConvexOrder.Embedding a b where
  map_next : ∀ x, point (s.next x) = t.next (point x)

def Embedding.refl (s : Successor a) : Embedding s s where
  toOrderedEmbedding := ConvexOrder.Embedding.refl a
  map_next _ := rfl

def Embedding.comp {Z : Type*} {C : Nested Z} {c : ConvexOrder C}
    {s : Successor a} {t : Successor b} {u : Successor c}
    (g : Embedding t u) (f : Embedding s t) : Embedding s u where
  toOrderedEmbedding := g.toOrderedEmbedding.comp f.toOrderedEmbedding
  map_next x := by
    change g.point (f.point (s.next x)) = u.next (g.point (f.point x))
    rw [f.map_next, g.map_next]

def IsClosed (s : Successor a) (S : Set X) : Prop := ∀ x ∈ S, s.next x ∈ S

def induce (s : Successor a) (S : Set X) (hS : s.IsClosed S) : Successor (a.induce S) where
  next x := ⟨s.next x.val, hS x.val x.property⟩
  sameP x := s.sameP x.val
  le_next x := s.le_next x.val
  least x y hP hxy := s.least x.val y.val hP hxy
  strict x h := by
    obtain ⟨y, hy, hxy⟩ := h
    exact s.strict x.val ⟨y.val, hy, hxy⟩

def inclusion (s : Successor a) (S : Set X) (hS : s.IsClosed S) :
    Embedding (s.induce S hS) s where
  toOrderedEmbedding := a.inclusion S
  map_next _ := rfl

end Successor

section Finite
variable [Finite X] (a : ConvexOrder A)

private noncomputable def nextCandidates (x : X) : Finset X := by
  classical
  letI := Fintype.ofFinite X
  exact Finset.univ.filter (fun y => A.P.r x y ∧ a.order.lt x y)

private theorem mem_nextCandidates {x y : X} :
    y ∈ nextCandidates a x ↔ A.P.r x y ∧ a.order.lt x y := by
  classical
  simp [nextCandidates]

private noncomputable def finiteNext (x : X) : X := by
  classical
  letI := a.order
  exact if h : (nextCandidates a x).Nonempty then (nextCandidates a x).min' h else x

private theorem finiteNext_mem {x : X}
    (h : ∃ y, A.P.r x y ∧ a.order.lt x y) :
    finiteNext a x ∈ nextCandidates a x := by
  classical
  letI := a.order
  have hn : (nextCandidates a x).Nonempty := by
    obtain ⟨y, hy⟩ := h
    exact ⟨y, (mem_nextCandidates a).mpr hy⟩
  simpa [finiteNext, hn] using (nextCandidates a x).min'_mem hn

noncomputable def finiteSuccessor : Successor a := by
  classical
  letI := a.order
  refine ⟨finiteNext a, ?_, ?_, ?_, ?_⟩
  · intro x
    by_cases h : ∃ y, A.P.r x y ∧ x < y
    · exact ((mem_nextCandidates a).mp (finiteNext_mem a h)).1
    · have hn : ¬(nextCandidates a x).Nonempty := by
        rintro ⟨y, hy⟩
        exact h ⟨y, (mem_nextCandidates a).mp hy⟩
      simpa [finiteNext, hn] using A.P.refl x
  · intro x
    by_cases h : ∃ y, A.P.r x y ∧ x < y
    · exact ((mem_nextCandidates a).mp (finiteNext_mem a h)).2.le
    · have hn : ¬(nextCandidates a x).Nonempty := by
        rintro ⟨y, hy⟩
        exact h ⟨y, (mem_nextCandidates a).mp hy⟩
      simp [finiteNext, hn]
  · intro x y hy hxy
    have hm := (mem_nextCandidates a).mpr ⟨hy, hxy⟩
    have hn : (nextCandidates a x).Nonempty := ⟨y, hm⟩
    simpa [finiteNext, hn] using (nextCandidates a x).min'_le y hm
  · intro x h
    exact ((mem_nextCandidates a).mp (finiteNext_mem a h)).2

/-- Every allowed ordered reduct has exactly one added-function expansion. -/
theorem existsUnique_successor : ∃! s : Successor a, True :=
  ⟨finiteSuccessor a, trivial, fun s _ => s.unique (finiteSuccessor a)⟩

end Finite
end CCO.ResetOrder.Counterexample.Nested.ConvexOrder
