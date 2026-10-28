import CCO.StrongExact.ThetaCycleContainsRight
import CCO.StrongExact.ThetaExceptLeftRank

/-!
# C07: every hard-theta cycle contains BOTH common formal roots

The local private-vertex degree theorem forces the two neighbors on
a genuine simple cycle to occupy opposite rank directions. If the
left root were missing, take a cycle vertex of maximum remaining
distance to the right root. It is private and has a compulsory
neighbor farther from the right root, contradicting maximality.

The dual global rank is not a new positive word or old colour:
it only measures finite original word positions. It is valid for
same-sort endpoints, repeated sorts and all old atomic palettes.

The two-root result is necessary for the eventual classification
as exactly two complete private branches; that classification is not
yet asserted here.
-/

universe u v w

namespace CCO.StrongExact

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {i j : ι}

theorem thetaCycle_contains_left
    (ws : List (PositiveWord S i j))
    (hLong : ∀ a : S.Atom i j,
      (PositiveWord.single a : PositiveWord S i j) ∉ ws)
    (C : SimpleCycle ((thetaEdgesOfLong S ws hLong).toDiagram)) :
    ∃ p : Fin C.length, C.vertices p = thetaLeft S ws := by
  classical
  by_contra hNo
  have hNoLeft (p : Fin C.length) :
      C.vertices p ≠ thetaLeft S ws := by
    intro h
    exact hNo ⟨p,h⟩
  let Rank : Fin C.length → Nat := fun p =>
    thetaExceptLeftRank S ws (C.vertices p)
  let p0 : Fin C.length := ⟨0,C.length_pos⟩
  have hPrivateOfNotRight (p : Fin C.length)
      (hRight : C.vertices p ≠ thetaRight S ws) :
      ∃ b : Fin ws.length, ∃ inner : wordInterior S (ws.get b),
        C.vertices p = (.inr ⟨b,inner⟩ : thetaVertices S ws) := by
    cases hp : C.vertices p with
    | inl x =>
        cases x with
        | false =>
            exact False.elim ((hNoLeft p) (by simpa only [thetaLeft] using hp))
        | true =>
            exact False.elim (hRight (by simpa only [thetaRight] using hp))
    | inr x =>
        refine ⟨x.1, x.2, ?_⟩
        cases x with
        | mk b inner => rfl
  have hSomePrivate : ∃ p : Fin C.length,
      ∃ b : Fin ws.length, ∃ inner : wordInterior S (ws.get b),
        C.vertices p = (.inr ⟨b,inner⟩ : thetaVertices S ws) := by
    by_cases hRight : C.vertices p0 = thetaRight S ws
    · let nxt := cyclicNext C.length_pos p0
      have hNxtRight : C.vertices nxt ≠ thetaRight S ws := by
        intro h
        exact (C.next_ne p0) (hRight.trans h.symm)
      obtain ⟨b,inner,h⟩ := hPrivateOfNotRight nxt hNxtRight
      exact ⟨nxt,b,inner,h⟩
    · obtain ⟨b,inner,h⟩ := hPrivateOfNotRight p0 hRight
      exact ⟨p0,b,inner,h⟩
  obtain ⟨pPrivate,bPrivate,innerPrivate,hPrivate⟩ := hSomePrivate
  have hPositive : 0 < Rank pPrivate := by
    change 0 < thetaExceptLeftRank S ws (C.vertices pPrivate)
    rw [hPrivate]
    exact thetaExceptLeftRank_private_pos S ws bPrivate innerPrivate
  letI : Fintype (Fin C.length) := inferInstance
  have hNonempty : (Finset.univ : Finset (Fin C.length)).Nonempty :=
    ⟨p0, Finset.mem_univ _⟩
  obtain ⟨p,_,hMax⟩ :=
    (Finset.univ : Finset (Fin C.length)).exists_max_image Rank hNonempty
  have hRankPos : 0 < Rank p := by
    have hle := hMax pPrivate (Finset.mem_univ _)
    omega
  have hpRight : C.vertices p ≠ thetaRight S ws := by
    intro hp
    have hr : Rank p = 0 := by
      change thetaExceptLeftRank S ws (C.vertices p) = 0
      rw [hp]
      rfl
    omega
  obtain ⟨b,inner,hHere⟩ := hPrivateOfNotRight p hpRight
  obtain ⟨q,t,hNext,hPrev,hDirections⟩ :=
    thetaCycle_private_two_sided S ws hLong C p b inner hHere
  have hNextNotLeft : thetaBranchPosition S ws b q ≠ thetaLeft S ws := by
    rw [← hNext]
    exact hNoLeft (cyclicNext C.length_pos p)
  have hPrevNotLeft : thetaBranchPosition S ws b t ≠ thetaLeft S ws := by
    rw [← hPrev]
    exact hNoLeft (cyclicPrev C.length_pos p)
  have hRankHere : Rank p =
      wordPositionRank S (ws.get b) (wordTarget S (ws.get b)) -
        wordPositionRank S (ws.get b) inner.val := by
    change thetaExceptLeftRank S ws (C.vertices p) = _
    rw [hHere]
    rfl
  have hRankNext : Rank (cyclicNext C.length_pos p) =
      wordPositionRank S (ws.get b) (wordTarget S (ws.get b)) -
        wordPositionRank S (ws.get b) q := by
    change thetaExceptLeftRank S ws
      (C.vertices (cyclicNext C.length_pos p)) = _
    rw [hNext]
    exact thetaExceptLeftRank_of_branch S ws b q hNextNotLeft
  have hRankPrev : Rank (cyclicPrev C.length_pos p) =
      wordPositionRank S (ws.get b) (wordTarget S (ws.get b)) -
        wordPositionRank S (ws.get b) t := by
    change thetaExceptLeftRank S ws
      (C.vertices (cyclicPrev C.length_pos p)) = _
    rw [hPrev]
    exact thetaExceptLeftRank_of_branch S ws b t hPrevNotLeft
  have hBoundNext : Rank (cyclicNext C.length_pos p) ≤ Rank p :=
    hMax _ (Finset.mem_univ _)
  have hBoundPrev : Rank (cyclicPrev C.length_pos p) ≤ Rank p :=
    hMax _ (Finset.mem_univ _)
  have hWordBoundNext := wordPositionRank_le_target S (ws.get b) q
  have hWordBoundPrev := wordPositionRank_le_target S (ws.get b) t
  have hWordBoundHere :=
    wordPositionRank_le_target S (ws.get b) inner.val
  rcases hDirections with hFwd | hBack
  · omega
  · omega

/-- Every old specified simple cycle in a long, genuinely typed
theta diagram visits both distinct shared roots. This does NOT yet
claim that its two private segments are whole word occurrences. -/
theorem thetaCycle_contains_both_roots
    (ws : List (PositiveWord S i j))
    (hLong : ∀ a : S.Atom i j,
      (PositiveWord.single a : PositiveWord S i j) ∉ ws)
    (C : SimpleCycle ((thetaEdgesOfLong S ws hLong).toDiagram)) :
    (∃ p : Fin C.length, C.vertices p = thetaLeft S ws) ∧
      (∃ p : Fin C.length, C.vertices p = thetaRight S ws) :=
  ⟨thetaCycle_contains_left S ws hLong C,
    thetaCycle_contains_right S ws hLong C⟩

end CCO.StrongExact
