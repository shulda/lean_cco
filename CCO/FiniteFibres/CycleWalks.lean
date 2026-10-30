import CCO.FiniteFibres.Target
import Mathlib.Combinatorics.SimpleGraph.Walk.Traversal
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Algebra.Ring.Parity

/-! The two elementary monochromatic cycle foldings, and componentwise
parity colourings. These proofs have no source homogeneity/Hasse input. -/
namespace CCO.FiniteFibres
open RelationalCompletion

variable {A : Type*} {G : SimpleGraph A} {x y : A}

def CyclicWalk (G : SimpleGraph A) (n : Nat) : Prop :=
  ∃ hn : 0 < n, ∃ f : Fin n → A,
    ∀ p, G.Adj (f p) (f (Atomic.cyclicNext hn p))

def padClosed (p : G.Walk x x) (h : G.Adj x y) : Nat → G.Walk x x
  | 0 => p
  | n + 1 => (padClosed p h n).append (.cons h (.cons h.symm .nil))

@[simp] theorem length_padClosed (p : G.Walk x x) (h : G.Adj x y) (n : Nat) :
    (padClosed p h n).length = p.length + 2 * n := by
  induction n with
  | zero => simp [padClosed]
  | succ n ih => simp [padClosed,SimpleGraph.Walk.length_append,ih]; omega

theorem cyclicWalk_of_closed (p : G.Walk x x) (hp : 0 < p.length) :
    CyclicWalk G p.length := by
  refine ⟨hp,fun j => p.getVert j.val,?_⟩
  intro j
  have hj := p.adj_getVert_succ j.isLt
  by_cases hlast : j.val + 1 = p.length
  · have hn : (Atomic.cyclicNext hp j).val = 0 := by simp [Atomic.cyclicNext,hlast]
    simpa only [hlast,SimpleGraph.Walk.getVert_length,hn,SimpleGraph.Walk.getVert_zero] using hj
  · have hlt : j.val + 1 < p.length := by omega
    have hn : (Atomic.cyclicNext hp j).val = j.val + 1 := by
      simp [Atomic.cyclicNext,Nat.mod_eq_of_lt hlt]
    simpa only [hn] using hj

theorem cyclicWalk_even (h : G.Adj x y) {n : Nat} (hn : 0 < n) (he : Even n) :
    CyclicWalk G n := by
  obtain ⟨k,hk⟩ := he
  let p := padClosed (SimpleGraph.Walk.nil : G.Walk x x) h k
  have hp : p.length = n := by simp [p,hk,two_mul]
  have hc := cyclicWalk_of_closed p (by omega)
  simpa only [hp] using hc

theorem cyclicWalk_longer (p : G.Walk x x) (h : G.Adj x y)
    {n : Nat} (hn : 0 < n) (hle : p.length ≤ n)
    (hpar : n % 2 = p.length % 2) : CyclicWalk G n := by
  let k := (n - p.length) / 2
  have hk : p.length + 2 * k = n := by omega
  let q := padClosed p h k
  have hq : q.length = n := by simpa only [q,length_padClosed] using hk
  have hc := cyclicWalk_of_closed q (by omega)
  simpa only [hq] using hc

theorem cyclicWalk_even_or_odd_above (p : G.Walk x x) (h : G.Adj x y)
    (hp : Odd p.length) {n : Nat} (hn : 0 < n) (hlarge : p.length < n) :
    CyclicWalk G n := by
  by_cases he : Even n
  · exact cyclicWalk_even h hn he
  · apply cyclicWalk_longer p h hn (Nat.le_of_lt hlarge)
    have ho : Odd n := Nat.not_even_iff_odd.mp he
    exact (Nat.odd_iff.mp ho).trans (Nat.odd_iff.mp hp).symm

/-- Absence of odd closed walks supplies an actual bipartition on each
connected component, including isolated vertices and the empty graph. -/
theorem no_odd_closed_walk_isBipartite (K : SimpleGraph A)
    (hno : ∀ x (p : K.Walk x x), ¬ Odd p.length) : K.IsBipartite := by
  classical
  let path (C : K.ConnectedComponent) (v : C) : K.Walk C.out v.val :=
    (C.reachable_of_mem_supp C.out_eq v.property).some
  let colour (C : K.ConnectedComponent) (v : C) : Fin 2 :=
    ⟨(path C v).length % 2,Nat.mod_lt _ (by decide)⟩
  have proper (C : K.ConnectedComponent) (x y : C)
      (hxy : C.toSimpleGraph.Adj x y) : colour C x ≠ colour C y := by
    intro heq
    have hm : (path C x).length % 2 = (path C y).length % 2 := congrArg Fin.val heq
    let edge : K.Adj x.val y.val := hxy
    let closed : K.Walk C.out C.out :=
      ((path C x).append edge.toWalk).append (path C y).reverse
    apply hno C.out closed
    apply Nat.odd_iff.mpr
    simp only [closed,SimpleGraph.Walk.length_append,SimpleGraph.Adj.length_toWalk,
      SimpleGraph.Walk.length_reverse]
    omega
  let fC : (C : K.ConnectedComponent) →
      C.toSimpleGraph →g SimpleGraph.completeGraph (Fin 2) :=
    fun C => { toFun := colour C,map_rel' := fun hxy => proper C _ _ hxy }
  exact ⟨K.homOfConnectedComponents fC⟩

end CCO.FiniteFibres
