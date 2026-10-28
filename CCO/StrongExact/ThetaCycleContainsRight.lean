import CCO.StrongExact.ThetaCycleContainsRoot
import CCO.StrongExact.ThetaExceptRightRank

/-!
# C07: any hard-theta simple cycle contains the RIGHT shared root

The underlying theta graph without the right root is a rooted forest
of private positive-word lines. A private vertex has precisely one
rank-increasing and one rank-decreasing neighbor along a simple cycle.
Choose the finite-cycle vertex of maximum private rank. Its compulsory
rank-increasing neighbor cannot be the left root (rank zero), and the
right root has been excluded, contradicting maximality.

This argument uses actual specified SIMPLE cycle constraints, the
independently proved private-vertex neighbor theorem, and only the
finite combinatorics of the formal word graph. It does not yet say
that the cycle consists of exactly two complete word branches.
-/

universe u v w

namespace CCO.StrongExact

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {i j : ι}

theorem thetaCycle_contains_right
    (ws : List (PositiveWord S i j))
    (hLong : ∀ a : S.Atom i j,
      (PositiveWord.single a : PositiveWord S i j) ∉ ws)
    (C : SimpleCycle ((thetaEdgesOfLong S ws hLong).toDiagram)) :
    ∃ p : Fin C.length, C.vertices p = thetaRight S ws := by
  classical
  by_contra hNo
  have hNoRight (p : Fin C.length) :
      C.vertices p ≠ thetaRight S ws := by
    intro h
    exact hNo ⟨p,h⟩
  let Rank : Fin C.length → Nat := fun p =>
    thetaExceptRightRank S ws (C.vertices p)
  let p0 : Fin C.length := ⟨0,C.length_pos⟩
  have hPrivateOfNotLeft (p : Fin C.length)
      (hLeft : C.vertices p ≠ thetaLeft S ws) :
      ∃ b : Fin ws.length, ∃ inner : wordInterior S (ws.get b),
        C.vertices p = (.inr ⟨b,inner⟩ : thetaVertices S ws) := by
    cases hp : C.vertices p with
    | inl x =>
        cases x with
        | false =>
            exact False.elim (hLeft (by simpa only [thetaLeft] using hp))
        | true =>
            exact False.elim ((hNoRight p) (by simpa only [thetaRight] using hp))
    | inr x =>
        refine ⟨x.1, x.2, ?_⟩
        cases x with
        | mk b inner => rfl
  have hSomePrivate : ∃ p : Fin C.length,
      ∃ b : Fin ws.length, ∃ inner : wordInterior S (ws.get b),
        C.vertices p = (.inr ⟨b,inner⟩ : thetaVertices S ws) := by
    by_cases hLeft : C.vertices p0 = thetaLeft S ws
    · let nxt := cyclicNext C.length_pos p0
      have hNxtLeft : C.vertices nxt ≠ thetaLeft S ws := by
        intro h
        exact (C.next_ne p0) (hLeft.trans h.symm)
      obtain ⟨b,inner,h⟩ := hPrivateOfNotLeft nxt hNxtLeft
      exact ⟨nxt,b,inner,h⟩
    · obtain ⟨b,inner,h⟩ := hPrivateOfNotLeft p0 hLeft
      exact ⟨p0,b,inner,h⟩
  obtain ⟨pPrivate,bPrivate,innerPrivate,hPrivate⟩ := hSomePrivate
  have hPositive : 0 < Rank pPrivate := by
    change 0 < thetaExceptRightRank S ws (C.vertices pPrivate)
    rw [hPrivate]
    exact thetaExceptRightRank_private_pos S ws bPrivate innerPrivate
  letI : Fintype (Fin C.length) := inferInstance
  have hNonempty : (Finset.univ : Finset (Fin C.length)).Nonempty :=
    ⟨p0, Finset.mem_univ _⟩
  obtain ⟨p,_,hMax⟩ :=
    (Finset.univ : Finset (Fin C.length)).exists_max_image Rank hNonempty
  have hRankPos : 0 < Rank p := by
    have hle := hMax pPrivate (Finset.mem_univ _)
    omega
  have hpLeft : C.vertices p ≠ thetaLeft S ws := by
    intro hp
    have hr : Rank p = 0 := by
      change thetaExceptRightRank S ws (C.vertices p) = 0
      rw [hp]
      rfl
    omega
  obtain ⟨b,inner,hHere⟩ := hPrivateOfNotLeft p hpLeft
  obtain ⟨q,t,hNext,hPrev,hDirections⟩ :=
    thetaCycle_private_two_sided S ws hLong C p b inner hHere
  have hNextNotRight : thetaBranchPosition S ws b q ≠ thetaRight S ws := by
    rw [← hNext]
    exact hNoRight (cyclicNext C.length_pos p)
  have hPrevNotRight : thetaBranchPosition S ws b t ≠ thetaRight S ws := by
    rw [← hPrev]
    exact hNoRight (cyclicPrev C.length_pos p)
  have hRankHere : Rank p =
      wordPositionRank S (ws.get b) inner.val := by
    change thetaExceptRightRank S ws (C.vertices p) = _
    rw [hHere]
    rfl
  have hRankNext : Rank (cyclicNext C.length_pos p) =
      wordPositionRank S (ws.get b) q := by
    change thetaExceptRightRank S ws
      (C.vertices (cyclicNext C.length_pos p)) = _
    rw [hNext]
    exact thetaExceptRightRank_of_branch S ws b q hNextNotRight
  have hRankPrev : Rank (cyclicPrev C.length_pos p) =
      wordPositionRank S (ws.get b) t := by
    change thetaExceptRightRank S ws
      (C.vertices (cyclicPrev C.length_pos p)) = _
    rw [hPrev]
    exact thetaExceptRightRank_of_branch S ws b t hPrevNotRight
  have hBoundNext : Rank (cyclicNext C.length_pos p) ≤ Rank p :=
    hMax _ (Finset.mem_univ _)
  have hBoundPrev : Rank (cyclicPrev C.length_pos p) ≤ Rank p :=
    hMax _ (Finset.mem_univ _)
  rcases hDirections with hFwd | hBack
  · omega
  · omega

end CCO.StrongExact
