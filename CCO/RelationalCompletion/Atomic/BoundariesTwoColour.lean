import CCO.RelationalCompletion.Atomic.BoundariesCycles
import CCO.RelationalCompletion.Atomic.BoundariesFiniteAge
import Mathlib.Tactic.NormNum

/-!
# The K2 homomorphic CCO boundary and the partial five-cycle

A specified simple cycle can map to K2 exactly when its length is even.
Using the actual odd-cycle extraction, cycle feasibility yields a single
colouring of an arbitrary input graph. Nevertheless the partial C5 has
no triangles and no completion to the age of K2.
-/
set_option maxRecDepth 10000
set_option maxHeartbeats 800000

namespace CCO.RelationalCompletion.Atomic.Boundaries
open SimpleGraph

/-- The one-atom semantic cycle condition. A cycle may have its own map
and nonadjacent vertices may coincide. -/
def CyclesFeasibleTwo {V : Type*} (G : SimpleGraph V) : Prop :=
  ∀ x (p : G.Walk x x), p.IsCycle → (cycleGraph p.length).IsBipartite

/-- Every feasible simple cycle is even, by the actual trichromatic odd
cycle obstruction. -/
theorem cycle_feasible_two_even {m : Nat} (hm : 3 ≤ m)
    (h : (cycleGraph m).IsBipartite) : Even m := by
  by_contra he
  have ho : Odd m := Nat.not_even_iff_odd.mp he
  have h3 := SimpleGraph.chromaticNumber_cycleGraph_of_odd m (by omega) ho
  have h2 := h.chromaticNumber_le
  rw [h3] at h2
  norm_num at h2

/-- Actual semantic homomorphic CCO for the one-atom age of K2.
No bound on carrier size, local finiteness or prechosen global colouring
is present. All unary tags and displayed edges are automatically allowed. -/
theorem cyclesFeasibleTwo_isBipartite {V : Type*} (G : SimpleGraph V)
    (hc : CyclesFeasibleTwo G) : G.IsBipartite := by
  apply no_odd_simple_cycle_isBipartite
  intro x p hp ho
  have he := cycle_feasible_two_even hp.three_le_length (hc x p hp)
  exact (Nat.not_even_iff_odd.mpr ho) he

/-- Conversely a whole graph colouring restricts to each simple cycle;
for this boundary it is enough to derive even cycle length. -/
theorem cyclesFeasibleTwo_of_even {V : Type*} (G : SimpleGraph V)
    (hc : ∀ x (p : G.Walk x x), p.IsCycle → Even p.length) : CyclesFeasibleTwo G := by
  intro x p hp
  exact SimpleGraph.IsBipartite.cycleGraph_of_even (hc x p hp)

/-- The partial five-cycle has no displayed triangle. -/
theorem fiveCycle_no_triangle : ¬∃ x y z : Fin 5,
    (cycleGraph 5).Adj x y ∧ (cycleGraph 5).Adj y z ∧ (cycleGraph 5).Adj z x := by
  decide

/-- Every three-vertex partial restriction really does admit a K2
homomorphism, including repetitions of chosen vertices. This is a finite
kernel computation on the displayed C5, not the general CCO proof above. -/
theorem fiveCycle_every_three_colourable : ∀ v : Fin 3 → Fin 5,
    ∃ c : Fin 3 → Fin 2, ∀ x y,
      (cycleGraph 5).Adj (v x) (v y) → c x ≠ c y := by
  decide

/-- The partial five-cycle has no homomorphism into K2. -/
theorem fiveCycle_no_two_colouring : ¬(cycleGraph 5).IsBipartite := by
  intro h
  have ho := cycle_feasible_two_even (m := 5) (by omega) h
  norm_num [Nat.even_iff] at ho

/-- A missing pair of the partial source remains genuinely unspecified:
C5 is not a complete input satisfying the triangle-fullness premise. -/
theorem fiveCycle_not_complete : ¬(cycleGraph 5).Adj (0 : Fin 5) (2 : Fin 5) := by
  decide

end CCO.RelationalCompletion.Atomic.Boundaries
