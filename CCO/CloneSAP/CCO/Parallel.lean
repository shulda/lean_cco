import CCO.CloneSAP.CCO.Components
import CCO.CloneSAP.CCO.TwoPaths

/-! C16: conflicting parallel owner labels are excluded by a literal simple
cycle, including the cases where either internal c-path has length zero. -/
universe u v w z
set_option backward.isDefEq.respectTransparency.types false
namespace CCO.CloneSAP.CCO
variable {ι : Type u} {X : ι → Type v} (S : AtomicSource.{u,v,w} ι X)
variable {V : Type z} (D : PartialDiagram (source S) V)

theorem old_parallel_labels
    (cycles : ∀ C : SimpleCycle D, CycleHom C)
    (x y x' y' : V) (hne : x ≠ y) (hne' : x' ≠ y')
    (a : S.Atom (D.vertexSort x) (D.vertexSort y))
    (b : S.Atom (D.vertexSort x') (D.vertexSort y'))
    (ha : D.edge x y hne = some (.inl a))
    (hb : D.edge x' y' hne' = some (.inl b))
    (hx : (cloneGraph S D).connectedComponentMk x = (cloneGraph S D).connectedComponentMk x')
    (hy : (cloneGraph S D).connectedComponentMk y = (cloneGraph S D).connectedComponentMk y') :
    (⟨D.vertexSort x,D.vertexSort y,some a⟩ : Σ i, Σ j, Option (S.Atom i j)) =
      ⟨D.vertexSort x',D.vertexSort y',some b⟩ := by
  classical
  by_cases same : x = x' ∧ y = y'
  · obtain ⟨rfl,rfl⟩ := same
    have hab := Sum.inl.inj (Option.some.inj (ha.symm.trans hb))
    cases hab
    rfl
  have different : x ≠ x' ∨ y ≠ y' := by
    by_cases hxx : x = x'
    · right
      intro hyy
      exact same ⟨hxx,hyy⟩
    · exact Or.inl hxx
  have hcomponents := old_edge_distinct_components S D cycles x y hne a ha
  obtain ⟨p,hp⟩ := (SimpleGraph.ConnectedComponent.exact hx).exists_isPath
  obtain ⟨q,hq⟩ := (SimpleGraph.ConnectedComponent.exact hy).exists_isPath
  let pp := p.mapLe (cloneGraph_le S D)
  let qq := q.mapLe (cloneGraph_le S D)
  have hp' : pp.IsPath := by simpa [pp] using hp
  have hq' : qq.IsPath := by simpa [qq] using hq
  have disjoint : pp.support.Disjoint qq.support := by
    intro c hc hd
    have hpc := clone_walk_component S D p (by simpa [pp] using hc)
    have hqc := clone_walk_component S D q (by simpa [qq] using hd)
    exact hcomponents (hpc.symm.trans hqc)
  let e : (graph D).Adj x y := ⟨hne,.inl a,ha⟩
  let e' : (graph D).Adj x' y' := ⟨hne',.inl b,hb⟩
  let cycle := twoPathWalk (graph D) pp qq e e'
  have hcycle : cycle.IsCycle := twoPathWalk_isCycle (graph D) pp qq hp' hq' e e' disjoint different
  obtain ⟨f,hf⟩ := walkCycle_edges D cycles cycle hcycle
  have hrealA := hf x y hne (.inl a) (by simp [cycle,twoPathWalk]) ha
  have hrealB := hf x' y' hne' (.inl b) (by simp [cycle,twoPathWalk,Sym2.eq_swap]) hb
  have hownerP := clone_walk_owner S D p f (by
    intro aa bb hh ee hm he
    apply hf aa bb hh (.inr ee) _ he
    simp [cycle,twoPathWalk,pp,hm])
  have hownerQ := clone_walk_owner S D q f (by
    intro aa bb hh ee hm he
    apply hf aa bb hh (.inr ee) _ he
    simp [cycle,twoPathWalk,qq,hm])
  have htags := congrArg₂ (taggedColour S) hownerP hownerQ
  have hca : taggedColour S ⟨D.vertexSort x,(f x).1⟩ ⟨D.vertexSort y,(f y).1⟩ =
      ⟨D.vertexSort x,D.vertexSort y,some a⟩ := by
    unfold taggedColour
    rw [(colour_old_iff S (f x) (f y) a).mp hrealA]
  have hcb : taggedColour S ⟨D.vertexSort x',(f x').1⟩ ⟨D.vertexSort y',(f y').1⟩ =
      ⟨D.vertexSort x',D.vertexSort y',some b⟩ := by
    unfold taggedColour
    rw [(colour_old_iff S (f x') (f y') b).mp hrealB]
  exact hca.symm.trans (htags.trans hcb)

end CCO.CloneSAP.CCO
