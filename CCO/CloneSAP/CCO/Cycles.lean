import CCO.CloneSAP.CCO.CycleProjection
import CCO.CloneSAP.CCO.GenericCycleBlocks
import CCO.CloneSAP.CCO.Realization

/-! C18--C21: every quotient cycle lifts through disjoint actual c-paths to
one genuine simple clone cycle. Applying ONLY original diversity HOM CCO
then gives an injective clone realization of the entire partial diagram. -/
universe u v w z
set_option backward.isDefEq.respectTransparency.types false
namespace CCO.CloneSAP.CCO
variable {ι : Type u} {X : ι → Type v} (S : AtomicSource.{u,v,w} ι X)
variable {V : Type z} (D : PartialDiagram (source S) V)

/-- The literal c-component quotient satisfies the ORIGINAL simple-cycle
criterion. No equality-labelled CCO theorem is an input. -/
theorem quotient_cycles (cycles : ∀ C : SimpleCycle D, CycleHom C) :
    ∀ C : SimpleCycle (quotientDiagram S D cycles), CycleHom C := by
  intro C
  let bs : Fin C.length → WalkBlock (graph D) := fun i => {
    first := (cycleEdge S D cycles C i).right
    last := (cycleEdge S D cycles C (cyclicNext C.length_pos i)).left
    walk := (cycleConnector S D cycles C i).walk.mapLe (cloneGraph_le S D) }
  have hp (i : Fin C.length) : (bs i).walk.IsPath := by
    simpa only [bs,SimpleGraph.Walk.isPath_mapLe] using
      (cycleConnector S D cycles C i).isPath
  have hd (i j : Fin C.length) (hne : i ≠ j) :
      (bs i).walk.support.Disjoint (bs j).walk.support := by
    simpa [bs] using connector_disjoint S D cycles C i j hne
  have hb (i : Fin C.length) :
      (graph D).Adj (bs i).last (bs (cyclicNext C.length_pos i)).first := by
    exact ⟨(cycleEdge S D cycles C (cyclicNext C.length_pos i)).ne,
      .inl (cycleEdge S D cycles C (cyclicNext C.length_pos i)).atom,
      (cycleEdge S D cycles C (cyclicNext C.length_pos i)).old_edge⟩
  obtain ⟨x,r,hr,hblocks,hbridges⟩ := cyclic_blocks (graph D) C.length_ge_three bs hp hd hb
  obtain ⟨f,hf⟩ := walkCycle_edges D cycles r hr
  have hOldMem (i : Fin C.length) :
      s((cycleEdge S D cycles C i).left,(cycleEdge S D cycles C i).right) ∈ r.edges := by
    obtain ⟨j,hj⟩ := RawExact.cyclicNext_surjective C.length_pos i
    have hm := hbridges j
    change s((cycleEdge S D cycles C (cyclicNext C.length_pos j)).left,
      (cycleEdge S D cycles C (cyclicNext C.length_pos j)).right) ∈ r.edges at hm
    rw [hj] at hm
    exact hm
  apply cycleHom_of_edge_realization S D cycles C f
  · intro i
    exact hf _ _ (cycleEdge S D cycles C i).ne (.inl (cycleEdge S D cycles C i).atom)
      (hOldMem i) (cycleEdge S D cycles C i).old_edge
  · intro i
    apply clone_walk_owner S D (cycleConnector S D cycles C i).walk f
    intro a b h e hm he
    apply hf a b h (.inr e) _ he
    apply hblocks i
    simpa only [bs,SimpleGraph.Walk.edges_mapLe_eq_edges] using hm

/-- C19--C21: original HOM CCO supplies the ACTUAL whole owner solution;
fresh clone indices then separate every original formal real vertex. -/
theorem cco_injective (cco : SemanticCCO.{u,v,z,w} S)
    (cycles : ∀ C : SimpleCycle D, CycleHom C) :
    ∃ f : DiagramHom D, f.IsInjective := by
  obtain ⟨f⟩ := cco (Component S D) (quotientDiagram S D cycles) (quotient_cycles S D cycles)
  exact realize_from_quotient S D cycles f

/-- The actual infinite pure clone construction preserves semantic HOM CCO.
It uses neither old AP/SAP, homogeneity nor triangle-definedness. -/
theorem cco_forward (cco : SemanticCCO.{u,v,z,w} S) :
    SemanticCCO.{u,v,z,w} (source S) := by
  intro V D cycles
  obtain ⟨f,_⟩ := cco_injective S D cco cycles
  exact ⟨f⟩

theorem cco_iff : SemanticCCO.{u,v,z,w} (source S) ↔ SemanticCCO.{u,v,z,w} S :=
  ⟨cco_reflects S,cco_forward S⟩

end CCO.CloneSAP.CCO
