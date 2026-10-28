import CCO.StrongExact.ThetaAdjacency
import CCO.StrongExact.ThetaLineRankExtra

/-!
# C07: every theta edge incident to a private vertex stays on its own line

A genuinely private formal point has an occurrence tag. The complete
candidate adjacency list contains ONLY genuine letters of the tagged
positive word or their reverses. Consequently no cycle can change its
private word branch except at one of the two shared formal roots.

This module does not postulate a cycle classification: it supplies a
verified, completely quantified local incidence invariant needed for one.
No original source model assumptions enter.
-/

universe u v w

namespace CCO.StrongExact

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {i j : ι}

theorem thetaPrivate_incident_letter
    (ws : List (PositiveWord S i j))
    (b : Fin ws.length)
    (p : wordInterior S (ws.get b))
    (y : thetaVertices S ws)
    (h : thetaAdjacent S ws (.inr ⟨b, p⟩) y) :
    ∃ e : wordEdgeIndex S (ws.get b),
      ((thetaBranchEdgeSource S ws b e = .inr ⟨b, p⟩ ∧
        thetaBranchEdgeTarget S ws b e = y) ∨
       (thetaBranchEdgeTarget S ws b e = .inr ⟨b, p⟩ ∧
        thetaBranchEdgeSource S ws b e = y)) := by
  obtain ⟨arc, harc, hsrc, hdst⟩ := h
  obtain ⟨c, e, hf | hr⟩ :=
    thetaArc_endpoints_on_branch S ws arc harc
  · have hbc : b = c :=
      private_embedded_position_same_branch S ws b c p
        (wordEdgeSource S (ws.get c) e) (by
          calc
            thetaBranchPosition S ws b p.val = .inr ⟨b, p⟩ :=
              thetaBranchPosition_interior S ws b p
            _ = arc.src := hsrc.symm
            _ = thetaBranchEdgeSource S ws c e := hf.1)
    subst c
    refine ⟨e, Or.inl ⟨?_, ?_⟩⟩
    · exact hf.1.symm.trans hsrc
    · exact hf.2.symm.trans hdst
  · have hbc : b = c :=
      private_embedded_position_same_branch S ws b c p
        (wordEdgeTarget S (ws.get c) e) (by
          calc
            thetaBranchPosition S ws b p.val = .inr ⟨b, p⟩ :=
              thetaBranchPosition_interior S ws b p
            _ = arc.src := hsrc.symm
            _ = thetaBranchEdgeTarget S ws c e := hr.1)
    subst c
    refine ⟨e, Or.inr ⟨?_, ?_⟩⟩
    · exact hr.1.symm.trans hsrc
    · exact hr.2.symm.trans hdst

/-- Every neighbor of a private theta point is on the SAME word
occurrence (possibly one of the two common roots). This is stronger
than merely ruling out edges between different private interiors. -/
theorem thetaPrivate_neighbor_on_line
    (ws : List (PositiveWord S i j))
    (b : Fin ws.length)
    (p : wordInterior S (ws.get b))
    (y : thetaVertices S ws)
    (h : thetaAdjacent S ws (.inr ⟨b, p⟩) y) :
    ∃ q : wordPositions S (ws.get b),
      y = thetaBranchPosition S ws b q := by
  obtain ⟨e, hf | hr⟩ :=
    thetaPrivate_incident_letter S ws b p y h
  · exact ⟨wordEdgeTarget S (ws.get b) e, hf.2.symm⟩
  · exact ⟨wordEdgeSource S (ws.get b) e, hr.2.symm⟩

/-- More precisely, an adjacent point is one rank *above* or one
rank *below* the given private point in its original positive word.
The middle sort is not changed by this purely graph-theoretic fact. -/
theorem thetaPrivate_neighbor_rank
    (ws : List (PositiveWord S i j))
    (b : Fin ws.length)
    (p : wordInterior S (ws.get b))
    (y : thetaVertices S ws)
    (h : thetaAdjacent S ws (.inr ⟨b, p⟩) y) :
    ∃ q : wordPositions S (ws.get b),
      y = thetaBranchPosition S ws b q ∧
      (wordPositionRank S (ws.get b) q =
         wordPositionRank S (ws.get b) p.val + 1 ∨
       wordPositionRank S (ws.get b) p.val =
         wordPositionRank S (ws.get b) q + 1) := by
  obtain ⟨e, hf | hr⟩ :=
    thetaPrivate_incident_letter S ws b p y h
  · have hpos : wordEdgeSource S (ws.get b) e = p.val :=
      (thetaBranchPosition_injective S ws b)
        (hf.1.trans (thetaBranchPosition_interior S ws b p).symm)
    refine ⟨wordEdgeTarget S (ws.get b) e, hf.2.symm, Or.inl ?_⟩
    rw [wordEdge_rank_step S (ws.get b) e, hpos]
  · have hpos : wordEdgeTarget S (ws.get b) e = p.val :=
      (thetaBranchPosition_injective S ws b)
        (hr.1.trans (thetaBranchPosition_interior S ws b p).symm)
    refine ⟨wordEdgeSource S (ws.get b) e, hr.2.symm, Or.inr ?_⟩
    rw [← hpos]
    exact wordEdge_rank_step S (ws.get b) e

end CCO.StrongExact
