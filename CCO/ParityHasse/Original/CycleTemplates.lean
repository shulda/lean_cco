import CCO.Finite
import Mathlib.Algebra.Ring.Parity
import Mathlib.Combinatorics.SimpleGraph.Walk.Traversal
import Mathlib.Combinatorics.SimpleGraph.Walk.Operations

/-! Even cycles fold onto one edge. Odd cycles can traverse any shorter
odd closed walk and add actual two-edge backtracks; no embedding is claimed. -/
namespace CCO.ParityHasse.Original
universe u
variable {A : Type u} {G : SimpleGraph A} {x y : A}

/-- A genuine cyclic adjacency map, allowed to repeat nonadjacent points. -/
def CyclicWalk (G : SimpleGraph A) (n : Nat) : Prop :=
  ∃ hn : 0 < n, ∃ f : Fin n → A, ∀ p,
    G.Adj (f p) (f (CCO.cyclicNext hn p))

/-- Append any number of literal two-step backtracks to an existing loop. -/
def padClosed (p : G.Walk x x) (h : G.Adj x y) : Nat → G.Walk x x
  | 0 => p
  | n + 1 => (padClosed p h n).append (.cons h (.cons h.symm .nil))

@[simp] theorem length_padClosed (p : G.Walk x x) (h : G.Adj x y) (n : Nat) :
    (padClosed p h n).length = p.length + 2 * n := by
  induction n with
  | zero => simp [padClosed]
  | succ n ih => simp [padClosed, SimpleGraph.Walk.length_append, ih]; omega

theorem cyclicWalk_of_closed (p : G.Walk x x) (hp : 0 < p.length) :
    CyclicWalk G p.length := by
  refine ⟨hp, fun j => p.getVert j.val, ?_⟩
  intro j
  have hj := p.adj_getVert_succ j.isLt
  by_cases hlast : j.val + 1 = p.length
  · have hn : (CCO.cyclicNext hp j).val = 0 := by simp [CCO.cyclicNext, hlast]
    simpa only [hlast, SimpleGraph.Walk.getVert_length, hn,
      SimpleGraph.Walk.getVert_zero] using hj
  · have hlt : j.val + 1 < p.length := by omega
    have hn : (CCO.cyclicNext hp j).val = j.val + 1 := by
      simp [CCO.cyclicNext, Nat.mod_eq_of_lt hlt]
    simpa only [hn] using hj

/-- An even cycle folds onto one actual edge. -/
theorem cyclicWalk_even (h : G.Adj x y) {n : Nat} (hn : 0 < n) (he : Even n) :
    CyclicWalk G n := by
  obtain ⟨k, hk⟩ := he
  let p := padClosed (SimpleGraph.Walk.nil : G.Walk x x) h k
  have hp : p.length = n := by simp [p, hk, two_mul]
  have hc := cyclicWalk_of_closed p (by omega)
  simpa only [hp] using hc

/-- The parity-compatible longer cycle goes once around the given closed
walk and then follows enough two-step backtracks. -/
theorem cyclicWalk_longer (p : G.Walk x x) (h : G.Adj x y)
    {n : Nat} (hn : 0 < n) (hle : p.length ≤ n)
    (hpar : n % 2 = p.length % 2) : CyclicWalk G n := by
  let k := (n - p.length) / 2
  have hk : p.length + 2 * k = n := by omega
  let q := padClosed p h k
  have hq : q.length = n := by simpa only [q, length_padClosed] using hk
  have hc := cyclicWalk_of_closed q (by omega)
  simpa only [hq] using hc

/-- These are the two templates consumed by original orbital parity. -/
theorem cyclicWalk_even_or_odd_above (p : G.Walk x x) (h : G.Adj x y)
    (hp : Odd p.length) {n : Nat} (hn : 0 < n)
    (hlarge : p.length < n) : CyclicWalk G n := by
  by_cases he : Even n
  · exact cyclicWalk_even h hn he
  · apply cyclicWalk_longer p h hn (Nat.le_of_lt hlarge)
    have ho : Odd n := Nat.not_even_iff_odd.mp he
    exact (Nat.odd_iff.mp ho).trans (Nat.odd_iff.mp hp).symm

end CCO.ParityHasse.Original
