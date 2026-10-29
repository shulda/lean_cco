import CCO.ProfileHelly.EdgeWalks

/-! Elementary actual-cycle cuts. Moving the first edge across an arc
does not assert any semantic completion of the new cycle. -/
universe u v z
namespace CCO.ProfileHelly.Network
variable {ι : Type u} {T : Table.{u,v} ι} {V : Type z} {sort : V → ι}
variable (D : Network T sort)
open SimpleGraph

theorem cycle_arcs_disjoint {x y : V} (p : D.graph.Walk x y) (q : D.graph.Walk x y)
    (hc : (p.append q.reverse).IsCycle) : Disjoint (D.internal p) (D.internal q) := by
  classical
  have hh := hc.support_nodup
  rw [Walk.tail_support_append,List.nodup_append'] at hh
  apply Finset.disjoint_left.mpr
  intro a hap haq
  obtain ⟨hap,hax,hay⟩ := (D.mem_internal p).mp hap
  obtain ⟨haq,_,_⟩ := (D.mem_internal q).mp haq
  have hp : a ∈ p.support.tail := ((p.mem_support_iff).mp hap).resolve_left hax
  have hqr : a ∈ q.reverse.support := by simpa only [Walk.support_reverse,List.mem_reverse] using haq
  have hq : a ∈ q.reverse.support.tail := ((q.reverse.mem_support_iff).mp hqr).resolve_left hay
  exact hh.2.2 hp hq

theorem cycle_cons_rotate {x y : V} (h : D.graph.Adj x y) (p : D.graph.Walk y x)
    (hc : (Walk.cons h p).IsCycle) : (p.concat h).IsCycle := by
  have hh := (Walk.cons_isCycle_iff p h).mp hc
  have hr : (Walk.cons h.symm p.reverse).IsCycle := by
    apply (Walk.cons_isCycle_iff p.reverse h.symm).mpr
    refine ⟨hh.1.reverse,?_⟩
    simpa only [Walk.edges_reverse,List.mem_reverse,Sym2.eq_swap] using hh.2
  simpa only [Walk.reverse_cons,Walk.reverse_reverse,← Walk.concat_eq_append] using hr.reverse

theorem cycle_move_head {x y z : V} (h : D.graph.Adj x y)
    (p : D.graph.Walk y z) (q : D.graph.Walk x z)
    (hc : ((Walk.cons h p).append q.reverse).IsCycle) :
    (p.append (Walk.cons h.symm q).reverse).IsCycle := by
  have hr := D.cycle_cons_rotate h (p.append q.reverse) hc
  simpa only [Walk.reverse_cons,Walk.concat_eq_append,Walk.append_assoc] using hr

theorem cycle_head_complement {x y z : V} (h : D.graph.Adj x y)
    (p : D.graph.Walk y z) (q : D.graph.Walk x z)
    (hc : ((Walk.cons h p).append q.reverse).IsCycle) :
    (q.append p.reverse).IsPath := by
  have hh := ((Walk.cons_isCycle_iff (p.append q.reverse) h).mp hc).1.reverse
  simpa only [Walk.reverse_append,Walk.reverse_reverse] using hh

theorem move_head_intersection {x y z : V} (h : D.graph.Adj x y)
    (p : D.graph.Walk y z) (q : D.graph.Walk x z) (hp : ¬p.Nil) (hq : ¬q.Nil) :
    (D.walkProfile (Walk.cons h p) Walk.not_nil_cons ∩ D.walkProfile q hq).Nonempty ↔
      (D.walkProfile p hp ∩ D.walkProfile (Walk.cons h.symm q) Walk.not_nil_cons).Nonempty := by
  change ((D.walkWord (Walk.cons h p) _).profile ∩ (D.walkWord q hq).profile).Nonempty ↔
    ((D.walkWord p hp).profile ∩ (D.walkWord (Walk.cons h.symm q) _).profile).Nonempty
  rw [D.walkWord_cons h p hp,D.walkWord_cons h.symm q hq]
  have hh := T.set_peirce_right {D.label h} (D.walkWord p hp).profile (D.walkWord q hq).profile
  change (T.product {D.label h} (D.walkWord p hp).profile ∩ (D.walkWord q hq).profile).Nonempty ↔
    ((D.walkWord p hp).profile ∩ T.product {D.label h.symm} (D.walkWord q hq).profile).Nonempty
  rw [D.label_reverse h]
  simpa only [T.opposite_singleton] using hh

end CCO.ProfileHelly.Network
