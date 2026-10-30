import CCO.ResetOrder.Counterexample.Successor
import CCO.ResetOrder.Counterexample.ConvexRanks
import Lean.Elab.Tactic.Omega

/-! Actual functionally closed subobjects meet every retained P-class in a
final segment. This explains heredity under the added total unary function. -/
namespace CCO.ResetOrder.Counterexample.Nested.ConvexOrder.Successor
variable {X : Type*} [Finite X] {A : Nested X} {a : ConvexOrder A}

/-- Every point later than a retained point in its P-component is retained. -/
theorem closed_final_segment (s : Successor a) {S : Set X} (hS : s.IsClosed S)
    {x y : X} (hx : x ∈ S) (hP : A.P.r x y) (hxy : a.order.le x y) : y ∈ S := by
  letI := a.order
  have step : ∀ n : ℕ, ∀ x : X, Nat.card X - orderRank a.order x = n →
      x ∈ S → A.P.r x y → x ≤ y → y ∈ S := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro z hz hzS hzP hzy
      by_cases heq : z = y
      · exact heq ▸ hzS
      · have hzlt : z < y := lt_of_le_of_ne hzy heq
        have hstrict := s.strict z ⟨y, hzP, hzlt⟩
        have hrank := (orderRank_lt_iff a.order z (s.next z)).mpr hstrict
        have hbound := orderRank_lt_card a.order (s.next z)
        have hdec : Nat.card X - orderRank a.order (s.next z) < n := by omega
        exact ih _ hdec (s.next z) rfl (hS z hzS)
          (A.P.trans (A.P.symm (s.sameP z)) hzP) (s.least z y hzP hzlt)
  exact step _ x rfl hx hP hxy

/-- Since the function is total and the point map is injective, preserving
its value also reflects its full graph. Domains are the entire carrier. -/
theorem graph_iff {Y : Type*} {B : Nested Y} {b : ConvexOrder B}
    {s : Successor a} {t : Successor b} (e : Embedding s t) (x y : X) :
    t.next (e.point x) = e.point y ↔ s.next x = y := by
  rw [← e.map_next]
  exact e.injective.eq_iff

theorem reflect_output {Y : Type*} {B : Nested Y} {b : ConvexOrder B}
    {s : Successor a} {t : Successor b} (e : Embedding s t) (x : X) (z : Y)
    (h : t.next (e.point x) = z) : ∃ y, s.next x = y ∧ e.point y = z :=
  ⟨s.next x, rfl, (e.map_next x).trans h⟩

/-- The graph-preserving induced embedding has an actually function-closed
image; no later image-closure callback is assumed. -/
theorem embedding_range_closed {Y : Type*} {B : Nested Y} {b : ConvexOrder B}
    {s : Successor a} {t : Successor b} (e : Embedding s t) :
    t.IsClosed (Set.range e.point) := by
  rintro _ ⟨x, rfl⟩
  exact ⟨s.next x, e.map_next x⟩

end CCO.ResetOrder.Counterexample.Nested.ConvexOrder.Successor
