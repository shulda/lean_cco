import CCO.StrongExact.ThetaLineEdges
import CCO.StrongExact.ThetaBranchInjective
import CCO.StrongExact.ThetaLineRank

/-!
# C07 theta's imported diversity edges have distinct formal endpoints

The actual old atom on each positive word letter is a genuine
STRONG diversity atom. After embedding its private branch into the
shared-root theta universe, the endpoints stay formally distinct
because the embedding is injective. In particular, repeated named
sorts DO NOT collapse the two formal endpoint vertices.

This small checked firewall must precede construction of the B001
partial diagram: its edge API takes an explicit `src ≠ dst` proof.
No artificial diagonal equality atom enters the generated graph.
-/

universe u v w

namespace CCO.StrongExact

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {i j : ι}

theorem thetaBranchEdge_distinct
    (ws : List (PositiveWord S i j))
    (b : Fin ws.length)
    (e : wordEdgeIndex S (ws.get b)) :
    thetaBranchEdgeSource S ws b e ≠
      thetaBranchEdgeTarget S ws b e := by
  intro he
  have hPositions :
      wordEdgeSource S (ws.get b) e =
        wordEdgeTarget S (ws.get b) e := by
    apply (thetaBranchPosition_injective S ws b)
    exact he
  exact (wordEdge_distinct S (ws.get b) e) hPositions

end CCO.StrongExact
