import CCO.OldIdempotentForest.VisibleBranches
import CCO.GuardedOldSeams.LiftGraphTheta
import CCO.StrongExact.ThetaArcWitness

/-! Every specified colour edge of the actual visible diagram belongs
to the original private-word graph. Thus its specified simple cycle has
the SAME cyclic enumeration in the concrete private-branch system. -/

universe u v w p q
namespace CCO.OldIdempotentForest
open CCO.StrongExact CCO.GuardedOldSeams CCO.GuardedTwoRoot
variable {ι : Type u} {X : ι → Type v} {S : AtomicSource.{u,v,w} ι X}
variable {P : Type p} {K : Type q} [Finite P] [Finite K]
namespace RootWordGeometry
variable (R : RootWordSystem S P K)

@[simp] theorem indexedVertex_at_position (b : Branch R)
    (z : wordPositions S (branchWord R b)) :
    indexedVertex R b (wordPositionEquiv S (branchWord R b) z) =
      R.branchPosition b.1 b.2 z := by
  unfold indexedVertex
  rw [Equiv.symm_apply_apply]

theorem theta_adjacent_graph (k : K) {z t : thetaVertices S (R.words k)}
    (h : thetaAdjacent S (R.words k) z t) : (graph R).Adj (R.embed k z) (R.embed k t) := by
  obtain ⟨arc,hArc,hz,ht⟩ := h
  obtain ⟨b,e,(⟨hs,hd⟩ | ⟨hs,hd⟩)⟩ := thetaArc_endpoints_on_branch S (R.words k) arc hArc
  · refine ⟨⟨k,b⟩,
      wordPositionEquiv S ((R.words k).get b) (wordEdgeSource S ((R.words k).get b) e),
      wordPositionEquiv S ((R.words k).get b) (wordEdgeTarget S ((R.words k).get b) e),?_,?_,?_⟩
    · left
      simpa only [wordPositionEquiv_val] using (wordEdge_rank_step S ((R.words k).get b) e).symm
    · exact (indexedVertex_at_position R ⟨k,b⟩ (wordEdgeSource S ((R.words k).get b) e)).trans
        (congrArg (R.embed k) (hs.symm.trans hz))
    · exact (indexedVertex_at_position R ⟨k,b⟩ (wordEdgeTarget S ((R.words k).get b) e)).trans
        (congrArg (R.embed k) (hd.symm.trans ht))
  · refine ⟨⟨k,b⟩,
      wordPositionEquiv S ((R.words k).get b) (wordEdgeTarget S ((R.words k).get b) e),
      wordPositionEquiv S ((R.words k).get b) (wordEdgeSource S ((R.words k).get b) e),?_,?_,?_⟩
    · right
      simpa only [wordPositionEquiv_val] using (wordEdge_rank_step S ((R.words k).get b) e).symm
    · exact (indexedVertex_at_position R ⟨k,b⟩ (wordEdgeTarget S ((R.words k).get b) e)).trans
        (congrArg (R.embed k) (hs.symm.trans hz))
    · exact (indexedVertex_at_position R ⟨k,b⟩ (wordEdgeSource S ((R.words k).get b) e)).trans
        (congrArg (R.embed k) (hd.symm.trans ht))

private theorem transport_option_none {s t s' t' : ι} (hs : s = s') (ht : t = t')
    (edge : Option (S.Atom s' t')) :
    transportAtomOption S hs ht edge = none ↔ edge = none := by
  cases hs
  cases ht
  rfl

theorem diagram_edge_adjacent (seed : RootWordSeeds S R)
    (x y : R.Vertex) (hxy : x ≠ y)
    (a : S.Atom (R.vertexSort x) (R.vertexSort y))
    (ha : (R.diagram seed).edge x y hxy = some a) : (graph R).Adj x y := by
  classical
  let D := R.gluing seed
  change D.unionEdge x y hxy = some a at ha
  have hw : Nonempty (D.PairWitness x y) := by
    by_contra hn
    have he : D.unionEdge x y hxy = none := by
      simp only [DiagramGluing.unionEdge,dif_neg hn]
    rw [he] at ha
    cases ha
  obtain ⟨k,z,t,hz,ht⟩ := Classical.choice hw
  subst x
  subst y
  have he := (D.unionEdge_on_piece k z t hxy).symm.trans ha
  have hzt : z ≠ t := fun h => hxy (congrArg (R.embed k) h)
  have hAdj : thetaAdjacent S (R.words k) z t := by
    by_contra hn
    have hNone : (thetaEdgesOfLiteralLines S (R.words k)
        (seed.left k) (seed.right k) (seed.lines k)).edge z t hzt = none := by
      change (if thetaAdjacent S (R.words k) z t then _ else none) = none
      rw [if_neg hn]
    have hCast := (transport_option_none (S := S) (R.embed_sort k z) (R.embed_sort k t) _).mpr hNone
    change transportAtomOption S (R.embed_sort k z) (R.embed_sort k t) _ = some a at he
    rw [hCast] at he
    cases he
  exact theta_adjacent_graph R k hAdj

/-- No root, private vertex, orientation or cyclic position is chosen
again when importing the actual colour cycle into private-path geometry. -/
noncomputable def cycleOfSpecified (seed : RootWordSeeds S R)
    (C : SimpleCycle (R.diagram seed)) : (privateBranchSystem R).Cycle where
  length := C.length
  three := C.length_ge_three
  positive := C.length_pos
  vertex := C.vertices
  adjacent p := by
    obtain ⟨a,ha⟩ := C.specified p
    exact diagram_edge_adjacent R seed _ _ (C.next_ne p) a ha

@[simp] theorem cycleOfSpecified_vertex (seed : RootWordSeeds S R)
    (C : SimpleCycle (R.diagram seed)) (p : Fin C.length) :
    (cycleOfSpecified R seed C).vertex p = C.vertices p := rfl

end RootWordGeometry
end CCO.OldIdempotentForest
