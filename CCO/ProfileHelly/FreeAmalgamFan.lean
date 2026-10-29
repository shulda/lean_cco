import CCO.ProfileHelly.Embeddings

/-! A fan reads every edge of a positive path. Its triangles need only
be legal at the fixed anchor; no complete extension is assumed. -/
universe u v z
namespace CCO.ProfileHelly.Network
open SimpleGraph
variable {ι : Type u} {T : Table.{u,v} ι} {V : Type z} {sort : V → ι}
variable (D : Network T sort)

structure Fan (anchor : V) (P : Set V) : Prop where
  edge : ∀ x, x ∈ P → anchor ≠ x → D.graph.Adj anchor x
  legal : ∀ x y, x ∈ P → y ∈ P → anchor ≠ x → x ≠ y → anchor ≠ y →
    ∀ a b c, D.edge anchor x = some a → D.edge x y = some b →
      D.edge anchor y = some c → T.triangle a b c

namespace Fan
variable {D} {anchor : V} {P : Set V} (F : D.Fan anchor P)
include F

/-- Algebraic fan propagation along a positive walk avoiding the anchor.
Each actual intermediate vertex is used; no maximal-segment assumption
can skip an extra visit to the common base. -/
theorem run (laws : TableLaws T) {x y : V} (p : D.graph.Walk x y)
    (hp : ¬p.Nil) (hAvoid : anchor ∉ p.support)
    (hP : ∀ x ∈ p.support, x ∈ P)
    (a : T.Atom (sort anchor) (sort x)) (c : T.Atom (sort anchor) (sort y))
    (ha : D.edge anchor x = some a) (hc : D.edge anchor y = some c) :
    c ∈ T.product {a} (D.walkProfile p hp) := by
  induction p with
  | nil => exact False.elim (hp .nil)
  | @cons x z y h p ih =>
    have hxMem : x ∈ (Walk.cons h p).support := Walk.start_mem_support (Walk.cons h p)
    have hzMem : z ∈ (Walk.cons h p).support := List.mem_cons_of_mem _ (Walk.start_mem_support p)
    have hax : anchor ≠ x := fun he =>
      hAvoid (Eq.mpr (congrArg (fun v => v ∈ (Walk.cons h p).support) he) hxMem)
    have haz : anchor ≠ z := fun he =>
      hAvoid (Eq.mpr (congrArg (fun v => v ∈ (Walk.cons h p).support) he) hzMem)
    have hxP : x ∈ P := hP x hxMem
    have hzP : z ∈ P := hP z hzMem
    cases p with
    | nil =>
        exact ⟨a,rfl,D.label h,rfl,F.legal x z hxP hzP hax h.ne haz a (D.label h) c ha (D.label_spec h) hc⟩
    | @cons z t y k p =>
        have hTailAvoid : anchor ∉ (Walk.cons k p).support := by
          intro hm
          exact hAvoid (List.mem_cons_of_mem _ hm)
        have hTailP : ∀ v ∈ (Walk.cons k p).support, v ∈ P :=
          fun v hv => hP v (List.mem_cons_of_mem _ hv)
        let e := F.edge z hzP haz
        let b := D.label e
        have hb : D.edge anchor z = some b := D.label_spec e
        have ht := ih Walk.not_nil_cons hTailAvoid hTailP b c hb hc
        have hbProd : b ∈ T.product {a} {D.label h} :=
          ⟨a,rfl,D.label h,rfl,F.legal x z hxP hzP hax h.ne haz a (D.label h) b ha (D.label_spec h) hb⟩
        have hm := T.product_mono (Set.singleton_subset_iff.mpr hbProd) (Set.Subset.refl _) ht
        rw [laws.associative] at hm
        exact hm

/-- The literal endpoint atom is in the profile of every SIMPLE positive
path from the anchor. No identity or empty positive profile is used. -/
theorem readout (laws : TableLaws T) {y : V} (p : D.graph.Path anchor y)
    (hxy : anchor ≠ y) (hP : ∀ x ∈ p.val.support, x ∈ P)
    (c : T.Atom (sort anchor) (sort y)) (hc : D.edge anchor y = some c) :
    c ∈ D.pathProfile hxy p := by
  rcases p with ⟨p,hPath⟩
  cases p with
  | nil => exact False.elim (hxy rfl)
  | @cons x z y h p =>
    cases p with
    | nil => exact (D.label_unique h c hc).symm
    | cons k p =>
        have hAvoid : anchor ∉ (Walk.cons k p).support :=
          (List.nodup_cons.mp hPath.support_nodup).1
        have hTailP : ∀ v ∈ (Walk.cons k p).support, v ∈ P :=
          fun v hv => hP v (List.mem_cons_of_mem _ hv)
        exact F.run laws (Walk.cons k p) Walk.not_nil_cons hAvoid hTailP
          (D.label h) c (D.label_spec h) hc

/-- In particular two base-to-base arcs contain the SAME literal base
atom. This includes the two-visit digon, with no fictitious simple 2-cycle. -/
theorem base_two_arcs (laws : TableLaws T) {y : V} (hxy : anchor ≠ y)
    (p q : D.graph.Path anchor y) (hp : ∀ x ∈ p.val.support, x ∈ P)
    (hq : ∀ x ∈ q.val.support, x ∈ P) (a : T.Atom (sort anchor) (sort y))
    (ha : D.edge anchor y = some a) :
    a ∈ D.pathProfile hxy p ∩ D.pathProfile hxy q :=
  ⟨F.readout laws p hxy hp a ha,F.readout laws q hxy hq a ha⟩

end Fan

/-- Move an anchor cut to an arbitrary pair of positive arcs. If the
anchor lies internally on one arc, fan propagation on the other arc and
set Peirce give the common atom. No semantic realization is introduced. -/
theorem fan_intersection_at (laws : TableLaws T) {anchor x y : V}
    (F : D.Fan anchor Set.univ) (hxy : x ≠ y) (p q : D.graph.Path x y)
    (hd : Disjoint (D.internal p.val) (D.internal q.val))
    (hp : anchor ∈ p.val.support) :
    (D.pathProfile hxy p ∩ D.pathProfile hxy q).Nonempty := by
  classical
  by_cases hax : anchor = x
  · subst anchor
    obtain ⟨a,ha⟩ := F.edge y (Set.mem_univ _) hxy
    exact ⟨a,F.readout laws p hxy (fun _ _ => Set.mem_univ _) a ha,
      F.readout laws q hxy (fun _ _ => Set.mem_univ _) a ha⟩
  by_cases hay : anchor = y
  · subst anchor
    obtain ⟨a,ha⟩ := F.edge x (Set.mem_univ _) hxy.symm
    have hp' := F.readout laws ⟨p.val.reverse,p.property.reverse⟩ hxy.symm
      (fun _ _ => Set.mem_univ _) a ha
    have hq' := F.readout laws ⟨q.val.reverse,q.property.reverse⟩ hxy.symm
      (fun _ _ => Set.mem_univ _) a ha
    change a ∈ D.walkProfile p.val.reverse (D.reverse_not_nil p.val (Walk.not_nil_of_ne hxy)) at hp'
    change a ∈ D.walkProfile q.val.reverse (D.reverse_not_nil q.val (Walk.not_nil_of_ne hxy)) at hq'
    rw [D.walkProfile_reverse laws p.val (Walk.not_nil_of_ne hxy)] at hp'
    rw [D.walkProfile_reverse laws q.val (Walk.not_nil_of_ne hxy)] at hq'
    exact ⟨T.conv a,hp',hq'⟩
  have hqAvoid : anchor ∉ q.val.support := by
    intro hq
    exact Finset.disjoint_left.mp hd
      ((D.mem_internal p.val).mpr ⟨hp,hax,hay⟩)
      ((D.mem_internal q.val).mpr ⟨hq,hax,hay⟩)
  obtain ⟨a,ha⟩ := F.edge x (Set.mem_univ _) hax
  obtain ⟨c,hc⟩ := F.edge y (Set.mem_univ _) hay
  let pL := D.prefixPath p hp
  let pR := D.suffixPath p hp
  have hpL := F.readout laws ⟨pL.val.reverse,pL.property.reverse⟩ hax
    (fun _ _ => Set.mem_univ _) a ha
  change a ∈ D.walkProfile pL.val.reverse (D.reverse_not_nil pL.val (Walk.not_nil_of_ne (Ne.symm hax))) at hpL
  rw [D.walkProfile_reverse laws pL.val (Walk.not_nil_of_ne (Ne.symm hax))] at hpL
  have hpR := F.readout laws pR hay (fun _ _ => Set.mem_univ _) c hc
  obtain ⟨a',ha',d,hdq,ht⟩ := F.run laws q.val (Walk.not_nil_of_ne hxy)
    hqAvoid (fun _ _ => Set.mem_univ _) a c ha hc
  have hae : a' = a := ha'
  subst a'
  refine ⟨d,?_,hdq⟩
  rw [D.prefix_suffix_profile laws hxy (Ne.symm hax) hay p hp]
  exact ⟨T.conv a,hpL,c,hpR,(T.peirce_right a d c).mp ht⟩

end CCO.ProfileHelly.Network
