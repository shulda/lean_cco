import CCO.StrongExact.ThetaCycleFirstArcPositions
import CCO.StrongExact.ThetaWordRankCoverage

/-!
# C07: every forward step of the first theta-cycle arc is a literal word edge

Once the actual first root arc covers every word position at its
original rank, each consecutive pair of cycle vertices is precisely
the source and target of the corresponding original diversity
letter. There are no identity steps, invented colours or skipped
word positions.
-/

universe u v w
namespace CCO.StrongExact

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {i j : ι}

theorem thetaCycle_left_arc_step_is_letter
    (ws : List (PositiveWord S i j))
    (hLong : ∀ a : S.Atom i j,
      (PositiveWord.single a : PositiveWord S i j) ∉ ws)
    (C : SimpleCycle ((thetaEdgesOfLong S ws hLong).toDiagram))
    (p q : Fin C.length) (k : Nat)
    (hp : C.vertices p = thetaLeft S ws)
    (hq : C.vertices q = thetaRight S ws)
    (hk : k < C.length)
    (hReached : thetaCycleAdvance C.length_pos p k = q)
    (b : Fin ws.length)
    (hArc : ∀ m : Nat, 0 < m → m < k →
      ∃ t : wordInterior S (ws.get b),
        C.vertices (thetaCycleAdvance C.length_pos p m) =
          (.inr ⟨b,t⟩ : thetaVertices S ws))
    (m : Nat) (hm : m < k) :
    ∃ e : wordEdgeIndex S (ws.get b),
      C.vertices (thetaCycleAdvance C.length_pos p m) =
        thetaBranchEdgeSource S ws b e ∧
      C.vertices (thetaCycleAdvance C.length_pos p (m + 1)) =
        thetaBranchEdgeTarget S ws b e := by
  have hFull := thetaCycle_left_arc_target_rank S ws hLong C
    p q k hp hq hk hReached b hArc
  have hmTarget : m <
      wordPositionRank S (ws.get b) (wordTarget S (ws.get b)) := by
    rw [hFull]
    exact hm
  obtain ⟨e,heRank⟩ :=
    wordEdgeSourceRank_exists S (ws.get b) m hmTarget
  have hs := thetaCycle_left_arc_all_positions S ws hLong C
    p q k hp hq hk hReached b hArc
      (wordEdgeSource S (ws.get b) e)
  have ht := thetaCycle_left_arc_all_positions S ws hLong C
    p q k hp hq hk hReached b hArc
      (wordEdgeTarget S (ws.get b) e)
  have heTargetRank : wordPositionRank S (ws.get b)
        (wordEdgeTarget S (ws.get b) e) = m + 1 := by
    rw [wordEdge_rank_step S (ws.get b) e, heRank]
  rw [heRank] at hs
  rw [heTargetRank] at ht
  refine ⟨e, ?_, ?_⟩
  · simpa only [thetaBranchEdgeSource] using hs
  · simpa only [thetaBranchEdgeTarget] using ht

end CCO.StrongExact
