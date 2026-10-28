import CCO.StrongExact.ThetaCycleLocal

/-! Orientation of a genuine simple theta cycle is forced along
private word positions. Once a cycle arrives at a private vertex
from lower rank, its next edge must increase the SAME branch rank.
This is local and does not assume a global cycle classification. -/

universe u v w
namespace CCO.StrongExact

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {i j : ι}

theorem thetaCycle_private_continues_up
    (ws : List (PositiveWord S i j))
    (hLong : ∀ a : S.Atom i j,
      (PositiveWord.single a : PositiveWord S i j) ∉ ws)
    (C : SimpleCycle ((thetaEdgesOfLong S ws hLong).toDiagram))
    (p : Fin C.length)
    (b : Fin ws.length)
    (t : wordInterior S (ws.get b))
    (hHere : C.vertices p =
      (.inr ⟨b,t⟩ : thetaVertices S ws))
    (hPrevLower : ∃ r : wordPositions S (ws.get b),
      C.vertices (cyclicPrev C.length_pos p) =
        thetaBranchPosition S ws b r ∧
      wordPositionRank S (ws.get b) r + 1 =
        wordPositionRank S (ws.get b) t.val) :
    ∃ q : wordPositions S (ws.get b),
      C.vertices (cyclicNext C.length_pos p) =
        thetaBranchPosition S ws b q ∧
      wordPositionRank S (ws.get b) q =
        wordPositionRank S (ws.get b) t.val + 1 := by
  obtain ⟨r0, hPrev0, hRank0⟩ := hPrevLower
  obtain ⟨q,r,hNext,hPrev,hDirections⟩ :=
    thetaCycle_private_two_sided S ws hLong C p b t hHere
  have hr : r = r0 :=
    (thetaBranchPosition_injective S ws b)
      (hPrev.symm.trans hPrev0)
  subst r
  rcases hDirections with hForward | hBackward
  · exact ⟨q,hNext,hForward.1⟩
  · have hrUp := hBackward.2
    omega

/-- A cycle similarly continues down a private word if it enters
from higher rank, by the local two-sided neighbor rule. -/
theorem thetaCycle_private_continues_down
    (ws : List (PositiveWord S i j))
    (hLong : ∀ a : S.Atom i j,
      (PositiveWord.single a : PositiveWord S i j) ∉ ws)
    (C : SimpleCycle ((thetaEdgesOfLong S ws hLong).toDiagram))
    (p : Fin C.length)
    (b : Fin ws.length)
    (t : wordInterior S (ws.get b))
    (hHere : C.vertices p =
      (.inr ⟨b,t⟩ : thetaVertices S ws))
    (hPrevHigher : ∃ r : wordPositions S (ws.get b),
      C.vertices (cyclicPrev C.length_pos p) =
        thetaBranchPosition S ws b r ∧
      wordPositionRank S (ws.get b) r =
        wordPositionRank S (ws.get b) t.val + 1) :
    ∃ q : wordPositions S (ws.get b),
      C.vertices (cyclicNext C.length_pos p) =
        thetaBranchPosition S ws b q ∧
      wordPositionRank S (ws.get b) q + 1 =
        wordPositionRank S (ws.get b) t.val := by
  obtain ⟨r0, hPrev0, hRank0⟩ := hPrevHigher
  obtain ⟨q,r,hNext,hPrev,hDirections⟩ :=
    thetaCycle_private_two_sided S ws hLong C p b t hHere
  have hr : r = r0 :=
    (thetaBranchPosition_injective S ws b)
      (hPrev.symm.trans hPrev0)
  subst r
  rcases hDirections with hForward | hBackward
  · have hrDown := hForward.2
    omega
  · exact ⟨q,hNext,hBackward.1⟩

end CCO.StrongExact
