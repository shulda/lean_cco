import CCO.ProfileHelly.Paths

/-! C27/C31: these are pure graph/cover statements. A walk crossing from
one exclusive factor side to the other has an INTERNAL overlap visit;
the two arcs of an actual simple cycle give TWO DISTINCT such visits. -/
universe u v z
namespace CCO.ProfileHelly
open SimpleGraph

/-- The edge-side hypothesis alone forces an internal overlap visit.
No compatibility of path orders, table algebra or completion is used. -/
theorem walk_crossing_overlap {V : Type z} (G : SimpleGraph V) (L R : Set V)
    (edges : ∀ {x y}, G.Adj x y → (x ∈ L ∧ y ∈ L) ∨ (x ∈ R ∧ y ∈ R))
    {x y : V} (p : G.Walk x y) (hx : x ∈ L \ R) (hy : y ∈ R \ L) :
    ∃ a, a ∈ p.support ∧ a ∈ L ∩ R ∧ a ≠ x ∧ a ≠ y := by
  induction p with
  | nil => exact False.elim (hy.2 hx.1)
  | @cons x z y h p ih =>
    have hzL : z ∈ L := by
      rcases edges h with hL | hR
      · exact hL.2
      · exact False.elim (hx.2 hR.1)
    by_cases hzR : z ∈ R
    · refine ⟨z,List.mem_cons_of_mem x p.start_mem_support,⟨hzL,hzR⟩,?_,?_⟩
      · intro he
        exact hx.2 (he ▸ hzR)
      · intro he
        exact hy.2 (he ▸ hzL)
    · obtain ⟨a,ha,haLR,_,hay⟩ := ih ⟨hzL,hzR⟩ hy
      exact ⟨a,List.mem_cons_of_mem x ha,haLR,
        fun he => hx.2 (he ▸ haLR.2),hay⟩

namespace Network
variable {ι : Type u} {T : Table.{u,v} ι} {V : Type z} {sort : V → ι}
variable (D : Network T sort)

/-- Two internally disjoint crossing arcs have distinct overlap visits.
This is the genuine two-base-visit fact, including crossed common orders. -/
theorem two_arc_overlap_visits (L R : Set V)
    (edges : ∀ {x y}, D.graph.Adj x y → (x ∈ L ∧ y ∈ L) ∨ (x ∈ R ∧ y ∈ R))
    {x y : V} (p q : D.graph.Path x y)
    (hd : Disjoint (D.internal p.val) (D.internal q.val))
    (hx : x ∈ L \ R) (hy : y ∈ R \ L) :
    ∃ a b, a ∈ L ∩ R ∧ b ∈ L ∩ R ∧ a ≠ b ∧
      a ∈ D.internal p.val ∧ b ∈ D.internal q.val := by
  obtain ⟨a,hap,ha,hax,hay⟩ := walk_crossing_overlap D.graph L R edges p.val hx hy
  obtain ⟨b,hbq,hb,hbx,hby⟩ := walk_crossing_overlap D.graph L R edges q.val hx hy
  have hpa : a ∈ D.internal p.val := (D.mem_internal _).mpr ⟨hap,hax,hay⟩
  have hqb : b ∈ D.internal q.val := (D.mem_internal _).mpr ⟨hbq,hbx,hby⟩
  exact ⟨a,b,ha,hb,fun he => Finset.disjoint_left.mp hd hpa (he.symm ▸ hqb),hpa,hqb⟩

/-- The crossing arcs really form a simple cycle; this is not an invented
two-edge cycle or a mere algebraic arc assumption. -/
theorem crossing_arcs_cycle (L R : Set V)
    (edges : ∀ {x y}, D.graph.Adj x y → (x ∈ L ∧ y ∈ L) ∨ (x ∈ R ∧ y ∈ R))
    {x y : V} (p q : D.graph.Path x y)
    (hd : Disjoint (D.internal p.val) (D.internal q.val))
    (hx : x ∈ L \ R) (hy : y ∈ R \ L) :
    (p.val.append q.val.reverse).IsCycle ∧
      ∃ a b, a ∈ L ∩ R ∧ b ∈ L ∩ R ∧ a ≠ b ∧
        a ∈ D.internal p.val ∧ b ∈ D.internal q.val := by
  have visits := D.two_arc_overlap_visits L R edges p q hd hx hy
  have hpq : p ≠ q := by
    intro he
    obtain ⟨a,ha,haLR,hax,hay⟩ := walk_crossing_overlap D.graph L R edges p.val hx hy
    have hm : a ∈ D.internal p.val := (D.mem_internal _).mpr ⟨ha,hax,hay⟩
    exact Finset.disjoint_left.mp hd hm (he ▸ hm)
  exact ⟨D.disjoint_paths_cycle p q hd hpq,visits⟩

/-- An arbitrary actual simple cycle containing vertices on BOTH exclusive
sides has at least two distinct overlap vertices in its actual support. -/
theorem mixed_cycle_overlap_visits (L R : Set V)
    (edges : ∀ {x y}, D.graph.Adj x y → (x ∈ L ∧ y ∈ L) ∨ (x ∈ R ∧ y ∈ R))
    {r : V} (c : D.graph.Walk r r) (hc : c.IsCycle)
    {x y : V} (hxs : x ∈ c.support) (hys : y ∈ c.support)
    (hx : x ∈ L \ R) (hy : y ∈ R \ L) :
    ∃ a b, a ∈ c.support ∧ b ∈ c.support ∧ a ∈ L ∩ R ∧ b ∈ L ∩ R ∧ a ≠ b := by
  classical
  let w := c.rotate x hxs
  have hw : w.IsCycle := hc.rotate hxs
  have hyw : y ∈ w.support := (Walk.mem_support_rotate_iff c x hxs).mpr hys
  have hxy : x ≠ y := fun he => hy.2 (he ▸ hx.1)
  let p : D.graph.Path x y := ⟨w.takeUntil y hyw,hw.isPath_takeUntil hyw⟩
  have hsplit : (w.takeUntil y hyw).append (w.dropUntil y hyw) = w := Walk.take_spec w hyw
  have ht : (w.dropUntil y hyw).IsPath := by
    have hcycle : ((w.takeUntil y hyw).append (w.dropUntil y hyw)).IsCycle := hsplit.symm ▸ hw
    exact hcycle.isPath_of_append_right (Walk.not_nil_of_ne hxy)
  let q : D.graph.Path x y := ⟨(w.dropUntil y hyw).reverse,ht.reverse⟩
  have hcycle : (p.val.append q.val.reverse).IsCycle := by
    simpa only [p,q,Walk.reverse_reverse,Walk.take_spec] using hw
  have hnodup := hcycle.support_nodup
  rw [Walk.tail_support_append,List.nodup_append'] at hnodup
  have hd : Disjoint (D.internal p.val) (D.internal q.val) := by
    apply Finset.disjoint_left.mpr
    intro a hap haq
    obtain ⟨hap,hax,hay⟩ := (D.mem_internal _).mp hap
    obtain ⟨haq,_,_⟩ := (D.mem_internal _).mp haq
    have hpa := (p.val.mem_support_iff.mp hap).resolve_left hax
    have hqr : a ∈ q.val.reverse.support := by simpa only [Walk.support_reverse,List.mem_reverse] using haq
    have hqa := (q.val.reverse.mem_support_iff.mp hqr).resolve_left hay
    exact hnodup.2.2 hpa hqa
  obtain ⟨a,b,ha,hb,hab,hap,hbq⟩ := D.two_arc_overlap_visits L R edges p q hd hx hy
  have has : a ∈ w.support := w.support_takeUntil_subset_support hyw ((D.mem_internal _).mp hap).1
  have hbs : b ∈ w.support := by
    have hh : b ∈ (w.dropUntil y hyw).support := by
      simpa only [q,Walk.support_reverse,List.mem_reverse] using ((D.mem_internal _).mp hbq).1
    exact w.support_dropUntil_subset_support hyw hh
  exact ⟨a,b,(Walk.mem_support_rotate_iff c x hxs).mp has,
    (Walk.mem_support_rotate_iff c x hxs).mp hbs,ha,hb,hab⟩

/-- C31: an overlap with at most one vertex permits no genuinely mixed
simple cycle. In particular the empty and singleton bases create none. -/
theorem cycle_in_one_factor_of_overlap_subsingleton (L R : Set V)
    (cover : ∀ x, x ∈ L ∨ x ∈ R)
    (edges : ∀ {x y}, D.graph.Adj x y → (x ∈ L ∧ y ∈ L) ∨ (x ∈ R ∧ y ∈ R))
    (small : (L ∩ R).Subsingleton) {r : V} (c : D.graph.Walk r r) (hc : c.IsCycle) :
    (∀ x ∈ c.support, x ∈ L) ∨ (∀ x ∈ c.support, x ∈ R) := by
  classical
  by_cases hL : ∀ x ∈ c.support, x ∈ L
  · exact Or.inl hL
  by_cases hR : ∀ x ∈ c.support, x ∈ R
  · exact Or.inr hR
  obtain ⟨y,hy⟩ := not_forall.mp hL
  obtain ⟨hys,hyL⟩ := not_imp.mp hy
  obtain ⟨x,hx⟩ := not_forall.mp hR
  obtain ⟨hxs,hxR⟩ := not_imp.mp hx
  obtain ⟨a,b,_,_,ha,hb,hab⟩ := D.mixed_cycle_overlap_visits L R edges c hc hxs hys
    ⟨(cover x).resolve_right hxR,hxR⟩ ⟨(cover y).resolve_left hyL,hyL⟩
  exact False.elim (hab (small ha hb))

end Network
end CCO.ProfileHelly
