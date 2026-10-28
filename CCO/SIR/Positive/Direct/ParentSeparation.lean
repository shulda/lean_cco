import CCO.SIR.Positive.Direct.CycleConsistency

/-! A specified n-edge cannot have endpoints in a single e/d component:
a simple e/d path together with that edge is an actual forbidden simple cycle. -/

universe z

namespace CCO.SIR.Positive.Direct

variable {V : Type z} (D : PartialDiagram source V)

private theorem edge_transport {x y x' y' : V} (hx : x = x') (hy : y = y')
    (h : x ≠ y) (h' : x' ≠ y') (a : Colour) :
    D.edge x y h = some a ↔ D.edge x' y' h' = some a := by
  cases hx
  cases hy
  rfl

theorem n_edge_not_ed_adj {x y : V} (h : x ≠ y)
    (hn : D.edge x y h = some .n) : ¬ (edGraph D).Adj x y := by
  rintro ⟨h',he | hd⟩
  · rw [hn] at he
    cases he
  · rw [hn] at hd
    cases hd

theorem n_edge_not_reachable
    (hcycles : ∀ C : SimpleCycle D, CycleHom C)
    {x y : V} (h : x ≠ y) (hn : D.edge x y h = some .n) :
    ¬ (edGraph D).Reachable x y := by
  classical
  intro hreach
  let path := hreach.some.toPath
  let p : (edGraph D).Walk x y := path.val
  have hp : p.IsPath := path.property
  have hp0 : p.length ≠ 0 :=
    fun hz => h (SimpleGraph.Walk.length_eq_zero_iff.mp hz).eq
  have hp1 : p.length ≠ 1 := fun ho =>
    n_edge_not_ed_adj D h hn (SimpleGraph.Walk.adj_of_length_eq_one ho)
  have hp2 : 2 ≤ p.length := by omega
  let q := p.reverse
  let r := q.mapLe (edGraph_le_specifiedGraph D)
  let hedge : (specifiedGraph D).Adj x y := ⟨h,.n,hn⟩
  let closed : (specifiedGraph D).Walk x x := .cons hedge r
  have hclosed : closed.IsCycle := by
    apply SimpleGraph.Walk.isCycle_iff_isPath_tail_and_le_length.mpr
    constructor
    · dsimp only [closed]
      rw [SimpleGraph.Walk.tail_cons]
      exact (SimpleGraph.Walk.isPath_copy r (SimpleGraph.Walk.getVert_zero r).symm rfl).mpr
        (hp.reverse.mapLe _)
    · simpa only [closed,r,q,SimpleGraph.Walk.length_cons,
        SimpleGraph.Walk.length_mapLe,SimpleGraph.Walk.length_reverse] using
        (show 3 ≤ p.length + 1 by omega)
  obtain ⟨f,hend,hsteps⟩ := realization_of_cycleWalk D
    (fun _ _ hh => hh) hcycles closed hclosed
  have hfirst : colour (f 0) (f 1) = some .n := by
    have hv0 : closed.getVert 0 = x := SimpleGraph.Walk.getVert_zero closed
    have hv1 : closed.getVert 1 = y := by
      change r.getVert 0 = y
      exact SimpleGraph.Walk.getVert_zero r
    have hh : closed.getVert 0 ≠ closed.getVert 1 := by
      simpa only [hv0,hv1] using h
    exact hsteps 0 (by simp [closed]) hh .n
      ((edge_transport D hv0 hv1 hh h .n).mpr hn)
  have hparentstep (n : ℕ) (hnb : n < q.length) :
      parent (f (n+1)) = parent (f (n+1+1)) := by
    have hadj := q.adj_getVert_succ hnb
    apply parent_of_realized_edge D hadj
    have hbound : n + 1 < closed.length := by
      simp only [closed,r,SimpleGraph.Walk.length_cons,
        SimpleGraph.Walk.length_mapLe]
      omega
    have heq0 : closed.getVert (n+1) = q.getVert n := by
      simp [closed,r,SimpleGraph.Walk.mapLe]
    have heq1 : closed.getVert (n+1+1) = q.getVert (n+1) := by
      simp [closed,r,SimpleGraph.Walk.mapLe]
    intro hxy a ha
    have hh : closed.getVert (n+1) ≠ closed.getVert (n+1+1) := by
      simpa only [heq0,heq1] using hxy
    exact hsteps (n+1) hbound hh a
      ((edge_transport D heq0 heq1 hh hxy a).mpr ha)
  have hparents (n : ℕ) : n ≤ q.length → parent (f 1) = parent (f (n+1)) := by
    induction n with
    | zero => intro _; rfl
    | succ n ih =>
        intro hle
        exact (ih (by omega)).trans (hparentstep n (by omega))
  have hlast : parent (f 1) = parent (f 0) := by
    have hh := hparents q.length le_rfl
    have hlen : closed.length = q.length + 1 := by simp [closed,r]
    rw [← hlen,hend] at hh
    exact hh
  exact ((colour_n _ _).mp hfirst) hlast.symm

end CCO.SIR.Positive.Direct
