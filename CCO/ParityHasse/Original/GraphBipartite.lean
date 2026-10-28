import Mathlib.Combinatorics.SimpleGraph.Bipartite
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Algebra.Ring.Parity

/-!
# No odd closed walks gives an actual two-colouring

Choose one base and one walk from that base to each vertex in each actual
connected component. The parity of the chosen walk length gives a proper
two-colouring. The construction permits arbitrary infinite carriers and
uses neither countability nor any local finiteness hypothesis.
-/

namespace CCO.ParityHasse.Original

/-- A same-parity edge would close an odd walk, so componentwise walk
parity assembles to an actual bipartite colouring of the whole graph. -/
theorem no_odd_closed_walk_isBipartite {A : Type*} (K : SimpleGraph A)
    (hno : ∀ x (p : K.Walk x x), ¬ Odd p.length) : K.IsBipartite := by
  classical
  let path (C : K.ConnectedComponent) (v : C) : K.Walk C.out v.val :=
    (C.reachable_of_mem_supp C.out_eq v.property).some
  let colour (C : K.ConnectedComponent) (v : C) : Fin 2 :=
    ⟨(path C v).length % 2, Nat.mod_lt _ (by decide)⟩
  have proper (C : K.ConnectedComponent) (x y : C)
      (hxy : C.toSimpleGraph.Adj x y) : colour C x ≠ colour C y := by
    intro heq
    have hmod : (path C x).length % 2 = (path C y).length % 2 := congrArg Fin.val heq
    let edge : K.Adj x.val y.val := hxy
    let closed : K.Walk C.out C.out :=
      ((path C x).append edge.toWalk).append (path C y).reverse
    apply hno C.out closed
    apply Nat.odd_iff.mpr
    simp only [closed, SimpleGraph.Walk.length_append,
      SimpleGraph.Adj.length_toWalk, SimpleGraph.Walk.length_reverse]
    omega
  let fC : (C : K.ConnectedComponent) →
      C.toSimpleGraph →g SimpleGraph.completeGraph (Fin 2) :=
    fun C => { toFun := colour C, map_rel' := fun hxy => proper C _ _ hxy }
  exact ⟨K.homOfConnectedComponents fC⟩

end CCO.ParityHasse.Original
