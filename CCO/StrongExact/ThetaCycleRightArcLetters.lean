import CCO.StrongExact.ThetaCycleRightArcPositions
import CCO.StrongExact.ThetaWordRankCoverage

/-!
# C07: the second theta-cycle arc traverses the old word letters backwards

The forward cyclic successor on the right-to-left root arc reads
the TARGET and then the SOURCE of each literal diversity word
letter, with no gaps or artificial equality labels. The required
converse colour is the already accepted B001 original typed converse.
-/

universe u v w
namespace CCO.StrongExact

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {i j : ι}

theorem thetaCycle_right_arc_step_is_reverse_letter
    (ws : List (PositiveWord S i j))
    (hLong : ∀ a : S.Atom i j,
      (PositiveWord.single a : PositiveWord S i j) ∉ ws)
    (C : SimpleCycle ((thetaEdgesOfLong S ws hLong).toDiagram))
    (q p : Fin C.length) (l : Nat)
    (hq : C.vertices q = thetaRight S ws)
    (hp : C.vertices p = thetaLeft S ws)
    (hl : l < C.length)
    (hReached : thetaCycleAdvance C.length_pos q l = p)
    (b : Fin ws.length)
    (hArc : ∀ m : Nat, 0 < m → m < l →
      ∃ t : wordInterior S (ws.get b),
        C.vertices (thetaCycleAdvance C.length_pos q m) =
          (.inr ⟨b,t⟩ : thetaVertices S ws))
    (m : Nat) (hm : m < l) :
    ∃ e : wordEdgeIndex S (ws.get b),
      C.vertices (thetaCycleAdvance C.length_pos q m) =
        thetaBranchEdgeTarget S ws b e ∧
      C.vertices (thetaCycleAdvance C.length_pos q (m + 1)) =
        thetaBranchEdgeSource S ws b e := by
  have hFull := thetaCycle_right_arc_target_rank S ws hLong C
    q p l hq hp hl hReached b hArc
  let n : Nat := l - (m + 1)
  have hn : n < wordPositionRank S (ws.get b)
      (wordTarget S (ws.get b)) := by
    dsimp only [n]
    rw [hFull]
    omega
  obtain ⟨e,heRank⟩ :=
    wordEdgeSourceRank_exists S (ws.get b) n hn
  have hs := thetaCycle_right_arc_all_positions S ws hLong C
    q p l hq hp hl hReached b hArc
      (wordEdgeSource S (ws.get b) e)
  have ht := thetaCycle_right_arc_all_positions S ws hLong C
    q p l hq hp hl hReached b hArc
      (wordEdgeTarget S (ws.get b) e)
  have heTargetRank : wordPositionRank S (ws.get b)
      (wordEdgeTarget S (ws.get b) e) = n + 1 := by
    rw [wordEdge_rank_step S (ws.get b) e, heRank]
  have hmTarget :
      wordPositionRank S (ws.get b) (wordTarget S (ws.get b)) -
        wordPositionRank S (ws.get b)
          (wordEdgeTarget S (ws.get b) e) = m := by
    rw [hFull, heTargetRank]
    dsimp only [n]
    omega
  have hmSource :
      wordPositionRank S (ws.get b) (wordTarget S (ws.get b)) -
        wordPositionRank S (ws.get b)
          (wordEdgeSource S (ws.get b) e) = m + 1 := by
    rw [hFull, heRank]
    dsimp only [n]
    omega
  rw [hmSource] at hs
  rw [hmTarget] at ht
  refine ⟨e, ?_, ?_⟩
  · simpa only [thetaBranchEdgeTarget] using ht
  · simpa only [thetaBranchEdgeSource] using hs

end CCO.StrongExact
