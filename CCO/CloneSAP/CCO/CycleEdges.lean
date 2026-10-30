import CCO.CloneSAP.CCO.Quotient
import CCO.RawExact.CycleIncidence

/-! Literal old-edge representatives and disjoint internal c-paths around
one genuine simple cycle of the actual component quotient. -/
universe u v w z
set_option backward.isDefEq.respectTransparency.types false
namespace CCO.CloneSAP.CCO
variable {ι : Type u} {X : ι → Type v} (S : AtomicSource.{u,v,w} ι X)
variable {V : Type z} (D : PartialDiagram (source S) V)
variable (cycles : ∀ C : SimpleCycle D, CycleHom C)
variable (C : SimpleCycle (quotientDiagram S D cycles))

structure CycleEdge (i : Fin C.length) where
  left : V
  right : V
  ne : left ≠ right
  atom : S.Atom (D.vertexSort left) (D.vertexSort right)
  left_component : component S D left = C.vertices i
  right_component : component S D right = C.vertices (cyclicNext C.length_pos i)
  old_edge : D.edge left right ne = some (.inl atom)
  cycle_atom : S.Atom (componentSort S D (C.vertices i))
    (componentSort S D (C.vertices (cyclicNext C.length_pos i)))
  specified : (quotientDiagram S D cycles).edge (C.vertices i)
    (C.vertices (cyclicNext C.length_pos i)) (C.next_ne i) = some cycle_atom
  tag_eq : (⟨D.vertexSort left,D.vertexSort right,some atom⟩ : Σ i, Σ j, Option (S.Atom i j)) =
    ⟨componentSort S D (C.vertices i),componentSort S D (C.vertices (cyclicNext C.length_pos i)),some cycle_atom⟩

noncomputable def cycleEdge (i : Fin C.length) : CycleEdge S D cycles C i := by
  apply Classical.choice
  obtain ⟨a,ha⟩ := C.specified i
  obtain ⟨x,y,h,b,hx,hy,he,htag⟩ := quotient_specified S D cycles ha
  exact ⟨⟨x,y,h,b,hx,hy,he,a,ha,htag⟩⟩

structure CycleConnector (i : Fin C.length) where
  walk : (cloneGraph S D).Walk (cycleEdge S D cycles C i).right
    (cycleEdge S D cycles C (cyclicNext C.length_pos i)).left
  isPath : walk.IsPath

noncomputable def cycleConnector (i : Fin C.length) : CycleConnector S D cycles C i := by
  apply Classical.choice
  have he : component S D (cycleEdge S D cycles C i).right =
      component S D (cycleEdge S D cycles C (cyclicNext C.length_pos i)).left :=
    (cycleEdge S D cycles C i).right_component.trans
      (cycleEdge S D cycles C (cyclicNext C.length_pos i)).left_component.symm
  obtain ⟨p,hp⟩ := (SimpleGraph.ConnectedComponent.exact he).exists_isPath
  exact ⟨⟨p,hp⟩⟩

/-- Each internal c-path stays entirely in its own quotient-cycle vertex. -/
theorem connector_component (i : Fin C.length) {x : V}
    (hx : x ∈ (cycleConnector S D cycles C i).walk.support) :
    component S D x = C.vertices (cyclicNext C.length_pos i) :=
  (clone_walk_component S D (cycleConnector S D cycles C i).walk hx).trans
    (cycleEdge S D cycles C i).right_component

/-- Genuine simplicity of the quotient cycle makes the path blocks disjoint,
including their endpoints; zero-length internal paths cause no exception. -/
theorem connector_disjoint (i j : Fin C.length) (hne : i ≠ j) :
    (cycleConnector S D cycles C i).walk.support.Disjoint
      (cycleConnector S D cycles C j).walk.support := by
  intro x hxi hxj
  have he := (connector_component S D cycles C i hxi).symm.trans
    (connector_component S D cycles C j hxj)
  exact hne (RawExact.cyclicNext_injective C.length_pos (C.vertices.injective he))

end CCO.CloneSAP.CCO
