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
end CCO.ProfileHelly.Network
