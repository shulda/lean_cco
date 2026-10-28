import CCO.StrongExact.ThetaCycleRightBranchSplit

/-!
# C07: distinct original private branches at both theta-cycle roots

Any genuine long-theta simple cycle has two cyclic neighbors at its
common left root and two at its common right root. Each pair of
neighbors lies on DIFFERENT original positive-word occurrences,
not merely on different vertices of one line.

This is a finite graph-theoretic invariant, independent of SemanticCCO,
SAP, any conditional Helly provider and the actual named sorts.
-/

universe u v w

namespace CCO.StrongExact

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {i j : ι}

theorem thetaCycle_left_has_two_branch_tags
    (ws : List (PositiveWord S i j))
    (hLong : ∀ a : S.Atom i j,
      (PositiveWord.single a : PositiveWord S i j) ∉ ws)
    (C : SimpleCycle ((thetaEdgesOfLong S ws hLong).toDiagram))
    (p : Fin C.length) (hp : C.vertices p = thetaLeft S ws) :
    ∃ b : Fin ws.length, ∃ c : Fin ws.length,
      ∃ t : wordInterior S (ws.get b),
      ∃ u : wordInterior S (ws.get c),
        b ≠ c ∧
        C.vertices (cyclicNext C.length_pos p) =
          (.inr ⟨b,t⟩ : thetaVertices S ws) ∧
        C.vertices (cyclicPrev C.length_pos p) =
          (.inr ⟨c,u⟩ : thetaVertices S ws) := by
  obtain ⟨b,t,hNext⟩ := thetaCycle_left_next_private S ws hLong C p hp
  obtain ⟨c,u,hPrev⟩ := thetaCycle_left_prev_private S ws hLong C p hp
  exact ⟨b,c,t,u,
    thetaCycle_left_neighbor_branches_distinct S ws hLong C p hp b c
      t u hNext hPrev,
    hNext,hPrev⟩

theorem thetaCycle_right_has_two_branch_tags
    (ws : List (PositiveWord S i j))
    (hLong : ∀ a : S.Atom i j,
      (PositiveWord.single a : PositiveWord S i j) ∉ ws)
    (C : SimpleCycle ((thetaEdgesOfLong S ws hLong).toDiagram))
    (p : Fin C.length) (hp : C.vertices p = thetaRight S ws) :
    ∃ b : Fin ws.length, ∃ c : Fin ws.length,
      ∃ t : wordInterior S (ws.get b),
      ∃ u : wordInterior S (ws.get c),
        b ≠ c ∧
        C.vertices (cyclicNext C.length_pos p) =
          (.inr ⟨b,t⟩ : thetaVertices S ws) ∧
        C.vertices (cyclicPrev C.length_pos p) =
          (.inr ⟨c,u⟩ : thetaVertices S ws) := by
  obtain ⟨b,t,hNext⟩ := thetaCycle_right_next_private S ws hLong C p hp
  obtain ⟨c,u,hPrev⟩ := thetaCycle_right_prev_private S ws hLong C p hp
  exact ⟨b,c,t,u,
    thetaCycle_right_neighbor_branches_distinct S ws hLong C p hp b c
      t u hNext hPrev,
    hNext,hPrev⟩

end CCO.StrongExact
