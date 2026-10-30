import CCO.CloneSAP.CCO.Quotient

/-! Once the actual diversity-only component diagram has an old solution,
one finite fresh-index choice realizes ALL original formal real vertices.
The original old CCO is applied only to this literal old diversity graph. -/
universe u v w z
set_option backward.isDefEq.respectTransparency.types false
namespace CCO.CloneSAP.CCO
variable {ι : Type u} {X : ι → Type v} (S : AtomicSource.{u,v,w} ι X)
variable {V : Type z} (D : PartialDiagram (source S) V)

theorem realize_from_quotient
    (cycles : ∀ C : SimpleCycle D, CycleHom C)
    (f : DiagramHom (quotientDiagram S D cycles)) :
    ∃ g : DiagramHom D, g.IsInjective := by
  apply lift_owner_assignment S D (fun x => f.point (component S D x))
  · intro x y h a ha
    exact f.preserves_edge (component S D x) (component S D y)
      (old_edge_distinct_components S D cycles x y h a ha) a
      (quotient_old_edge S D cycles x y h a ha)
  · intro x y h e he
    have hc : component S D x = component S D y :=
      SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj
        (show (cloneGraph S D).Adj x y from ⟨h,e,he⟩)
    exact congrArg f.image hc

end CCO.CloneSAP.CCO
