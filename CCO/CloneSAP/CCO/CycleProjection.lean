import CCO.CloneSAP.CCO.CycleEdges

/-! Project the literal clone-cycle solution back to the actual old quotient
cycle. All casts retain original sorts; old atoms are kept, not weakened. -/
universe u v w z
set_option backward.isDefEq.respectTransparency.types false
namespace CCO.CloneSAP.CCO
variable {ι : Type u} {X : ι → Type v} (S : AtomicSource.{u,v,w} ι X)
variable {V : Type z} (D : PartialDiagram (source S) V)
variable (cycles : ∀ C : SimpleCycle D, CycleHom C)
variable (C : SimpleCycle (quotientDiagram S D cycles))

private theorem sigma_cast {i j : ι} (h : i = j) (p : X i) :
    (⟨j,h ▸ p⟩ : Sigma X) = ⟨i,p⟩ := by cases h; rfl

/-- Internal readout lemma: the actual old edges and equality of owners
along the actual intervening c-paths realize the quotient cycle. -/
theorem cycleHom_of_edge_realization
    (f : ∀ x : V, Carrier X (D.vertexSort x))
    (edges : ∀ i,
      (source S).colour (f (cycleEdge S D cycles C i).left)
        (f (cycleEdge S D cycles C i).right) = some (.inl (cycleEdge S D cycles C i).atom))
    (joins : ∀ i,
      (⟨D.vertexSort (cycleEdge S D cycles C i).right,
        (f (cycleEdge S D cycles C i).right).1⟩ : Sigma X) =
      ⟨D.vertexSort (cycleEdge S D cycles C (cyclicNext C.length_pos i)).left,
        (f (cycleEdge S D cycles C (cyclicNext C.length_pos i)).left).1⟩) :
    CycleHom C := by
  let point : ∀ i : Fin C.length, X (componentSort S D (C.vertices i)) := fun i =>
    (congrArg (componentSort S D) (cycleEdge S D cycles C i).left_component) ▸
      (f (cycleEdge S D cycles C i).left).1
  have hpoint (i : Fin C.length) :
      (⟨componentSort S D (C.vertices i),point i⟩ : Sigma X) =
        ⟨D.vertexSort (cycleEdge S D cycles C i).left,
          (f (cycleEdge S D cycles C i).left).1⟩ := sigma_cast _ _
  refine ⟨point,?_⟩
  intro i a ha
  have hi : (cycleEdge S D cycles C i).cycle_atom = a :=
    Option.some.inj ((cycleEdge S D cycles C i).specified.symm.trans ha)
  have hleft := hpoint i
  have hright := (hpoint (cyclicNext C.length_pos i)).trans (joins i).symm
  have hold : taggedColour S
      ⟨D.vertexSort (cycleEdge S D cycles C i).left,(f (cycleEdge S D cycles C i).left).1⟩
      ⟨D.vertexSort (cycleEdge S D cycles C i).right,(f (cycleEdge S D cycles C i).right).1⟩ =
      ⟨D.vertexSort (cycleEdge S D cycles C i).left,
        D.vertexSort (cycleEdge S D cycles C i).right,some (cycleEdge S D cycles C i).atom⟩ := by
    unfold taggedColour
    rw [(colour_old_iff S _ _ _).mp (edges i)]
  have htag := (congrArg₂ (taggedColour S) hleft hright).trans
    (hold.trans (cycleEdge S D cycles C i).tag_eq)
  rw [hi] at htag
  exact eq_of_heq (Sigma.mk.inj (eq_of_heq (Sigma.mk.inj htag).2)).2

end CCO.CloneSAP.CCO
