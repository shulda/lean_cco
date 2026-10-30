import CCO.CloneSAP.CCO.GraphCycles
import CCO.CloneSAP.CCO.Lift

/-! Literal c-components and the first simple-cycle obstruction. -/
universe u v w z
set_option backward.isDefEq.respectTransparency.types false
namespace CCO.CloneSAP.CCO
variable {ι : Type u} {X : ι → Type v} (S : AtomicSource.{u,v,w} ι X)
variable {V : Type z} (D : PartialDiagram (source S) V)

/-- Only the specified new clone-diversity edges, with isolated vertices kept. -/
def cloneGraph : SimpleGraph V where
  Adj x y := ∃ h : x ≠ y, ∃ e : PLift (D.vertexSort x = D.vertexSort y),
    D.edge x y h = some (.inr e)
  symm.symm := by
    rintro x y ⟨h,e,he⟩
    exact ⟨h.symm,⟨e.down.symm⟩,(D.edge_reverse x y h (.inr e)).mp he⟩
  loopless.irrefl := by rintro x ⟨h,_⟩; exact h rfl

theorem cloneGraph_le : cloneGraph S D ≤ graph D := by
  rintro x y ⟨h,e,he⟩
  exact ⟨h,.inr e,he⟩

theorem clone_walk_sort {x y : V} (p : (cloneGraph S D).Walk x y) :
    D.vertexSort x = D.vertexSort y := by
  induction p with
  | nil => rfl
  | @cons x a y h p ih => exact h.choose_spec.choose.down.trans ih

theorem clone_walk_component {x y a : V} (p : (cloneGraph S D).Walk x y)
    (ha : a ∈ p.support) :
    (cloneGraph S D).connectedComponentMk a = (cloneGraph S D).connectedComponentMk x := by
  induction p with
  | @nil x =>
    have he : a = x := by simpa using ha
    exact congrArg (cloneGraph S D).connectedComponentMk he
  | @cons x b y h p ih =>
    rcases List.mem_cons.mp ha with rfl | ha
    · rfl
    · exact (ih ha).trans (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj h).symm

/-- D05/C14: components carry a definite original named sort. -/
def componentSort : (cloneGraph S D).ConnectedComponent → ι :=
  SimpleGraph.ConnectedComponent.lift D.vertexSort
    (fun _ _ p _ => clone_walk_sort S D p)

@[simp] theorem componentSort_mk (x : V) :
    componentSort S D ((cloneGraph S D).connectedComponentMk x) = D.vertexSort x := rfl

/-- Actual clone-edge realizations keep the SAME old owner along every c-walk. -/
theorem clone_walk_owner {x y : V} (p : (cloneGraph S D).Walk x y)
    (f : ∀ x : V, Carrier X (D.vertexSort x))
    (realizes : ∀ a b h e, s(a,b) ∈ p.edges → D.edge a b h = some (.inr e) →
      (source S).colour (f a) (f b) = some (.inr e)) :
    (⟨D.vertexSort x,(f x).1⟩ : Sigma X) = ⟨D.vertexSort y,(f y).1⟩ := by
  induction p with
  | nil => rfl
  | @cons x a y h p ih =>
    obtain ⟨hne,e,he⟩ := h
    have hfirst := realizes x a hne e (by simp) he
    have ho := ((colour_clone_iff S (f x) (f a) e).mp hfirst).1
    exact ho.trans (ih (fun aa bb hh ee hm hee =>
      realizes aa bb hh ee (by simp only [SimpleGraph.Walk.edges_cons]; exact List.mem_cons_of_mem _ hm) hee))

/-- C15: an old diversity edge cannot be internal to a c-component. A
shortest c-path plus that old edge is a GENUINE simple diversity cycle. -/
theorem old_edge_distinct_components
    (cycles : ∀ C : SimpleCycle D, CycleHom C)
    (x y : V) (hne : x ≠ y)
    (a : S.Atom (D.vertexSort x) (D.vertexSort y))
    (ha : D.edge x y hne = some (.inl a)) :
    (cloneGraph S D).connectedComponentMk x ≠
      (cloneGraph S D).connectedComponentMk y := by
  intro heq
  have hr := SimpleGraph.ConnectedComponent.exact heq
  obtain ⟨p,hp⟩ := hr.symm.exists_isPath
  let q := p.mapLe (cloneGraph_le S D)
  have hq : q.IsPath := by simpa only [q,SimpleGraph.Walk.isPath_mapLe] using hp
  have hold : (graph D).Adj x y := ⟨hne,.inl a,ha⟩
  have hnmem : s(x,y) ∉ q.edges := by
    intro hm
    have hc : (cloneGraph S D).Adj x y := p.adj_of_mem_edges (by simpa [q] using hm)
    obtain ⟨h,e,he⟩ := hc
    have hh := ha.symm.trans he
    cases hh
  let cycle := SimpleGraph.Walk.cons hold q
  have hcycle : cycle.IsCycle :=
    (SimpleGraph.Walk.cons_isCycle_iff q hold).mpr ⟨hq,hnmem⟩
  obtain ⟨f,hf⟩ := walkCycle_edges D cycles cycle hcycle
  have holdReal := hf x y hne (.inl a) (by simp [cycle]) ha
  have howners : (⟨D.vertexSort y,(f y).1⟩ : Sigma X) = ⟨D.vertexSort x,(f x).1⟩ := by
    apply clone_walk_owner S D p f
    intro aa bb hh e hm he
    apply hf aa bb hh (.inr e) _ he
    simp only [cycle,SimpleGraph.Walk.edges_cons,List.mem_cons]
    exact Or.inr (by simpa [q] using hm)
  have oldReal := (colour_old_iff S (f x) (f y) a).mp holdReal
  exact S.atomRel_ne oldReal howners.symm

end CCO.CloneSAP.CCO
