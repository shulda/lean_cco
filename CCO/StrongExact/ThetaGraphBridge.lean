import CCO.StrongExact.ThetaEdgesBuild
import CCO.StrongExact.ThetaAdjacency

/-!
# C07: the actual typed theta diagram has precisely the intended old edges

The chosen original diversity-labelled B001 PartialDiagram edge relation
is equivalent to the literal finite candidate arc list, and hence to
the underlying undirected simple theta graph. It does not invent any
additional edge or conflate same-sort formal vertices.

This is a bridge between real typed edge semantics and the purely finite
combinatorial graph, needed for the later exact simple-cycle classification.
-/

universe u v w

namespace CCO.StrongExact

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {i j : ι}

/-- A hard theta's edge is specified exactly when the finite
candidate arc list contains that ordered pair. -/
theorem thetaEdgesOfLong_edge_iff_arc
    (ws : List (PositiveWord S i j))
    (hLong : ∀ a : S.Atom i j,
      (PositiveWord.single a : PositiveWord S i j) ∉ ws)
    (x y : thetaVertices S ws) (hxy : x ≠ y) :
    (∃ a : S.Atom (thetaVertexSort S ws x)
        (thetaVertexSort S ws y),
        (thetaEdgesOfLong S ws hLong).edge x y hxy = some a) ↔
      thetaAdjacent S ws x y := by
  constructor
  · rintro ⟨a, ha⟩
    change thetaEdge S ws x y hxy = some a at ha
    unfold thetaEdge at ha
    cases hChoice : thetaArcAtChoice S ws x y with
    | none =>
        simp [hChoice] at ha
    | some candidate =>
        exact ⟨candidate.arc, candidate.mem,
          candidate.src_eq, candidate.dst_eq⟩
  · rintro ⟨arc, hm, hs, ht⟩
    let candidate : ThetaArcAt S ws x y :=
      ⟨arc, hm, hs, ht⟩
    refine ⟨candidate.atom, ?_⟩
    change thetaEdge S ws x y hxy = some candidate.atom
    unfold thetaEdge
    rw [thetaArcAtChoice_eq_some S ws hLong candidate]
    rfl

/-- The same edge set appears in the actual B001 partial diagram and
in the independent finite undirected simple graph on its formal points. -/
theorem thetaDiagram_edge_iff_graph
    (ws : List (PositiveWord S i j))
    (hLong : ∀ a : S.Atom i j,
      (PositiveWord.single a : PositiveWord S i j) ∉ ws)
    (x y : thetaVertices S ws) (hxy : x ≠ y) :
    (∃ a : S.Atom (thetaVertexSort S ws x)
        (thetaVertexSort S ws y),
        ((thetaEdgesOfLong S ws hLong).toDiagram).edge x y hxy =
          some a) ↔
      (thetaSimpleGraph S ws).Adj x y := by
  exact thetaEdgesOfLong_edge_iff_arc S ws hLong x y hxy

/-- No direct root edge can occur in the actual typed theta diagram
of genuinely long positive words. This is the real-diagram corollary,
not merely an auxiliary assertion about a list of candidates. -/
theorem thetaDiagram_no_root_edge
    (ws : List (PositiveWord S i j))
    (hLong : ∀ a : S.Atom i j,
      (PositiveWord.single a : PositiveWord S i j) ∉ ws) :
    ¬ ∃ a : S.Atom i j,
      ((thetaEdgesOfLong S ws hLong).toDiagram).edge
        (thetaLeft S ws) (thetaRight S ws)
        (thetaLeft_ne_right S ws) = some a := by
  intro h
  have ha : thetaAdjacent S ws (thetaLeft S ws)
      (thetaRight S ws) :=
    (thetaEdgesOfLong_edge_iff_arc S ws hLong
      (thetaLeft S ws) (thetaRight S ws)
      (thetaLeft_ne_right S ws)).mp h
  exact thetaAdjacent_no_root_pair S ws hLong ha


/-- Each enumerated original positive-word letter is actually realized
by every homomorphism of the constructed typed theta diagram. The
source and target sorts are the literal positional sorts of that
word, not universally identified root labels. -/
theorem thetaDiagramHom_respects_forward
    (ws : List (PositiveWord S i j))
    (hLong : ∀ a : S.Atom i j,
      (PositiveWord.single a : PositiveWord S i j) ∉ ws)
    (f : DiagramHom ((thetaEdgesOfLong S ws hLong).toDiagram))
    (b : Fin ws.length) (e : wordEdgeIndex S (ws.get b)) :
    S.colour
      (f.point (thetaBranchEdgeSource S ws b e))
      (f.point (thetaBranchEdgeTarget S ws b e)) =
      some (thetaBranchEdgeAtom S ws b e) := by
  exact f.preserves_edge
    (thetaBranchEdgeSource S ws b e)
    (thetaBranchEdgeTarget S ws b e)
    (thetaBranchEdge_distinct S ws b e)
    (thetaBranchEdgeAtom S ws b e)
    (thetaEdgesOfLong_preserves_forward S ws hLong b e)

end CCO.StrongExact
