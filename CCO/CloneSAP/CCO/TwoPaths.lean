import CCO.CloneSAP.CCO.GraphCycles

/-! Two disjoint simple paths, possibly of length zero, joined by two
different cross edges form a genuine simple cycle. -/
universe z
namespace CCO.CloneSAP.CCO
variable {V : Type z} (G : SimpleGraph V)

def twoPathWalk {x x' y y' : V} (p : G.Walk x x') (q : G.Walk y y')
    (h : G.Adj x y) (h' : G.Adj x' y') : G.Walk x x :=
  .cons h (q.append (.cons h'.symm p.reverse))

theorem twoPathWalk_isCycle {x x' y y' : V} (p : G.Walk x x') (q : G.Walk y y')
    (hp : p.IsPath) (hq : q.IsPath) (h : G.Adj x y) (h' : G.Adj x' y')
    (disjoint : p.support.Disjoint q.support) (different : x ≠ x' ∨ y ≠ y') :
    (twoPathWalk G p q h h').IsCycle := by
  apply SimpleGraph.Walk.isCycle_iff_isPath_tail_and_le_length.mpr
  constructor
  · apply SimpleGraph.Walk.IsPath.mk'
    have hs : (twoPathWalk G p q h h').tail.support = q.support ++ p.support.reverse := by
      simp [twoPathWalk,SimpleGraph.Walk.support_append]
    rw [hs,List.nodup_append]
    refine ⟨hq.support_nodup,List.nodup_reverse.mpr hp.support_nodup,?_⟩
    intro a ha b hb heq
    subst b
    exact disjoint (List.mem_reverse.mp hb) ha
  · have hlen : (twoPathWalk G p q h h').length = p.length + q.length + 2 := by
      simp [twoPathWalk]
      omega
    rw [hlen]
    by_contra hh
    have hp0 : p.length = 0 := by omega
    have hq0 : q.length = 0 := by omega
    exact different.elim (fun he => he (SimpleGraph.Walk.eq_of_length_eq_zero hp0))
      (fun he => he (SimpleGraph.Walk.eq_of_length_eq_zero hq0))

end CCO.CloneSAP.CCO
