import CCO.StrongExact.ThetaCycleRightArcLength
import CCO.StrongExact.ThetaExceptLeftRank

/-!
# C07: complementary theta cycle arc covers every original word position

Each original private word position of rank r occurs at the cyclic
position whose forward distance from the right root is targetRank-r.
The two common roots are literal and distinct even if their named
sort labels agree. This is finite typed graph geometry, not CCO/Helly.
-/

universe u v w
namespace CCO.StrongExact

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {i j : ι}

theorem thetaCycle_right_arc_all_positions
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
    (z : wordPositions S (ws.get b)) :
    C.vertices (thetaCycleAdvance C.length_pos q
      (wordPositionRank S (ws.get b) (wordTarget S (ws.get b)) -
        wordPositionRank S (ws.get b) z)) =
      thetaBranchPosition S ws b z := by
  have hFull := thetaCycle_right_arc_target_rank S ws hLong C
    q p l hq hp hl hReached b hArc
  let m := wordPositionRank S (ws.get b) (wordTarget S (ws.get b)) -
    wordPositionRank S (ws.get b) z
  have hBound := wordPositionRank_le_target S (ws.get b) z
  have hBoundM : m ≤ l := by
    dsimp only [m]
    rw [hFull]
    omega
  by_cases hmZero : m = 0
  · have hzRank :
        wordPositionRank S (ws.get b) z =
        wordPositionRank S (ws.get b)
          (wordTarget S (ws.get b)) := by
      dsimp only [m] at hmZero
      omega
    have hz : z = wordTarget S (ws.get b) :=
      (wordPositionRank_injective S (ws.get b)) hzRank
    subst z
    simp only [Nat.sub_self, thetaCycleAdvance]
    exact hq.trans (thetaBranchPosition_target S ws b).symm
  · by_cases hmEnd : m = l
    · have hzZero : wordPositionRank S (ws.get b) z = 0 := by
        dsimp only [m] at hmEnd
        rw [hFull] at hmEnd
        omega
      have hzSource : z = wordSource S (ws.get b) :=
        (wordPositionRank_injective S (ws.get b)) (by
          rw [wordSource_rank_zero S (ws.get b)]
          exact hzZero)
      subst z
      rw [wordSource_rank_zero S (ws.get b), hFull,
        Nat.sub_zero, hReached]
      exact hp.trans (thetaBranchPosition_source S ws b).symm
    · have hmPos : 0 < m := by omega
      have hmLt : m < l := by omega
      obtain ⟨t,ht,hRank⟩ :=
        thetaCycle_right_arc_remaining_rank_matches_distance
          S ws hLong C q p l hq hp hl hReached b hArc
          m hmPos hmLt
      have hzEq : z = t.val := by
        apply (wordPositionRank_injective S (ws.get b))
        have hzEqRank : wordPositionRank S (ws.get b) z =
            wordPositionRank S (ws.get b) t.val := by
          dsimp only [m] at hRank
          omega
        exact hzEqRank
      subst z
      have hRankDiff :
          wordPositionRank S (ws.get b) (wordTarget S (ws.get b)) -
              wordPositionRank S (ws.get b) t.val = m := by
        dsimp only [m]
        rfl
      rw [hRankDiff]
      exact ht.trans (thetaBranchPosition_interior S ws b t).symm

end CCO.StrongExact
