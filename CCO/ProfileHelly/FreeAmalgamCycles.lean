import CCO.ProfileHelly.FreeAmalgamFan
import CCO.ProfileHelly.EmbeddingImages

/-! Direct algebraic compatibility of the free partial amalgam. Every
base anchor gives an actual fan; paths avoiding the overlap stay in one
complete factor. No profile Helly or completion theorem is used. -/
universe u v z y w
namespace CCO.ProfileHelly.Network
open SimpleGraph
variable {ι : Type u} {T : Table.{u,v} ι}
variable {V : Type z} {L : Type y} {R : Type w}
variable {sort : V → ι} {leftSort : L → ι} {rightSort : R → ι}
variable (D : Network T sort)

/-- A path cannot switch between two sides without visiting their actual
intersection. This elementary fact needs neither finiteness nor simplicity. -/
theorem walk_side (A B : Set V)
    (hEdges : ∀ x y, D.graph.Adj x y → (x ∈ A ∧ y ∈ A) ∨ (x ∈ B ∧ y ∈ B))
    {x y : V} (p : D.graph.Walk x y)
    (hAvoid : ∀ v ∈ p.support, ¬(v ∈ A ∧ v ∈ B)) (hx : x ∈ A) :
    ∀ v ∈ p.support, v ∈ A := by
  induction p with
  | @nil x =>
      intro v hv
      have he : v = x := by simpa only [Walk.support_nil,List.mem_singleton] using hv
      exact he ▸ hx
  | @cons x z y h p ih =>
      have hz : z ∈ A := by
        rcases hEdges x z h with hl | hr
        · exact hl.2
        · exact False.elim (hAvoid x (Walk.start_mem_support (Walk.cons h p)) ⟨hx,hr.1⟩)
      have ht := ih (fun v hv => hAvoid v (List.mem_cons_of_mem _ hv)) hz
      intro v hv
      rcases List.mem_cons.mp hv with he | ht'
      · exact he ▸ hx
      · exact ht v ht'

namespace Embedding
variable {D} (C : CompleteNetwork T leftSort) (l : Embedding C.toNetwork D)

theorem imageFan (anchor : V) (ha : ∃ x, l.point x = anchor) :
    D.Fan anchor (Set.range l.point) where
  edge v hv hne := l.complete_image C anchor v ha hv hne
  legal x y hx hy hax hxy hay a b c ha' hb' hc' :=
    l.legal_image C anchor x y ha hx hy hax hxy hay a b c ha' hb' hc'
end Embedding

variable (C : CompleteNetwork T leftSort) (E : CompleteNetwork T rightSort)
variable (l : Embedding C.toNetwork D) (r : Embedding E.toNetwork D)
variable (covered : ∀ v, (∃ x, l.point x = v) ∨ (∃ y, r.point y = v))
variable (edge_factor : ∀ x y, D.graph.Adj x y →
  (∃ a b, l.point a = x ∧ l.point b = y) ∨ (∃ a b, r.point a = x ∧ r.point b = y))

include covered edge_factor in
/-- Every overlap vertex is a universal anchor. Each incident recorded
triangle belongs to the complete factor containing its opposite edge. -/
theorem overlapFan (anchor : V) (hl : ∃ x, l.point x = anchor) (hr : ∃ y, r.point y = anchor) :
    D.Fan anchor Set.univ where
  edge v _ hne := by
    rcases covered v with hv | hv
    · exact l.complete_image C anchor v hl hv hne
    · exact r.complete_image E anchor v hr hv hne
  legal x y _ _ hax hxy hay a b c ha hb hc := by
    rcases edge_factor x y ⟨b,hb⟩ with ⟨p,q,hp,hq⟩ | ⟨p,q,hp,hq⟩
    · exact l.legal_image C anchor x y hl ⟨p,hp⟩ ⟨q,hq⟩ hax hxy hay a b c ha hb hc
    · exact r.legal_image E anchor x y hr ⟨p,hp⟩ ⟨q,hq⟩ hax hxy hay a b c ha hb hc

include C E l r covered edge_factor in
/-- ALL specified simple cycles of the exact union of complete factors
are algebraically compatible. The proof retains literal factor/base
colours and covers empty or singleton overlaps without a base-size premise. -/
theorem algebraic_of_complete_cover (laws : TableLaws T) : D.Algebraic := by
  intro x y hxy p q hd _hpq
  classical
  by_cases hBase : ∃ b, (b ∈ p.val.support ∨ b ∈ q.val.support) ∧
      (∃ a, l.point a = b) ∧ (∃ a, r.point a = b)
  · obtain ⟨b,hb,hl,hr⟩ := hBase
    let F := overlapFan D C E l r covered edge_factor b hl hr
    rcases hb with hp | hq
    · exact D.fan_intersection_at laws F hxy p q hd hp
    · obtain ⟨a,ha,hb⟩ := D.fan_intersection_at laws F hxy q p hd.symm hq
      exact ⟨a,hb,ha⟩
  · have hNoP : ∀ b ∈ p.val.support,
        ¬(b ∈ Set.range l.point ∧ b ∈ Set.range r.point) := by
      intro b hb hBoth
      exact hBase ⟨b,Or.inl hb,hBoth.1,hBoth.2⟩
    have hNoQ : ∀ b ∈ q.val.support,
        ¬(b ∈ Set.range l.point ∧ b ∈ Set.range r.point) := by
      intro b hb hBoth
      exact hBase ⟨b,Or.inr hb,hBoth.1,hBoth.2⟩
    have hSides : ∀ a b, D.graph.Adj a b →
        (a ∈ Set.range l.point ∧ b ∈ Set.range l.point) ∨
        (a ∈ Set.range r.point ∧ b ∈ Set.range r.point) := by
      intro a b hab
      rcases edge_factor a b hab with ⟨u,v,hu,hv⟩ | ⟨u,v,hu,hv⟩
      · exact Or.inl ⟨⟨u,hu⟩,⟨v,hv⟩⟩
      · exact Or.inr ⟨⟨u,hu⟩,⟨v,hv⟩⟩
    rcases covered x with hx | hx
    · have hp := D.walk_side (Set.range l.point) (Set.range r.point) hSides p.val hNoP hx
      have hq := D.walk_side (Set.range l.point) (Set.range r.point) hSides q.val hNoQ hx
      let F := l.imageFan C x hx
      obtain ⟨a,ha⟩ := F.edge y (hp y (Walk.end_mem_support p.val)) hxy
      exact ⟨a,F.readout laws p hxy hp a ha,F.readout laws q hxy hq a ha⟩
    · have hSides' : ∀ a b, D.graph.Adj a b →
          (a ∈ Set.range r.point ∧ b ∈ Set.range r.point) ∨
          (a ∈ Set.range l.point ∧ b ∈ Set.range l.point) :=
        fun a b hab => (hSides a b hab).symm
      have hp := D.walk_side (Set.range r.point) (Set.range l.point) hSides' p.val
        (fun b hb hBoth => hNoP b hb ⟨hBoth.2,hBoth.1⟩) hx
      have hq := D.walk_side (Set.range r.point) (Set.range l.point) hSides' q.val
        (fun b hb hBoth => hNoQ b hb ⟨hBoth.2,hBoth.1⟩) hx
      let F := r.imageFan E x hx
      obtain ⟨a,ha⟩ := F.edge y (hp y (Walk.end_mem_support p.val)) hxy
      exact ⟨a,F.readout laws p hxy hp a ha,F.readout laws q hxy hq a ha⟩

end CCO.ProfileHelly.Network
