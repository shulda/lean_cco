import CCO.StrongExact.ThetaPrivateIncidence

/-!
# C07: at most one private-branch neighbor on each rank side

At a private formal vertex, all adjacent theta vertices lie on its
own word line, exactly one rank up or one rank down. A pair of
different neighbors must therefore lie on OPPOSITE rank sides.

This gives the local graph-theoretic degree-two bound needed in
the simple-cycle classification, without any graph-completion axiom,
original CCO/SAP premise, or hidden identity atom.
-/

universe u v w

namespace CCO.StrongExact

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {i j : ι}

private theorem private_neighbor_eq_of_same_rank
    (ws : List (PositiveWord S i j))
    (b : Fin ws.length)
    {y z : thetaVertices S ws}
    {q r : wordPositions S (ws.get b)}
    (hy : y = thetaBranchPosition S ws b q)
    (hz : z = thetaBranchPosition S ws b r)
    (hRank : wordPositionRank S (ws.get b) q =
      wordPositionRank S (ws.get b) r) : y = z := by
  have hp : q = r :=
    (wordPositionRank_injective S (ws.get b)) hRank
  exact hy.trans ((congrArg (thetaBranchPosition S ws b) hp).trans hz.symm)

/-- Two distinct neighbors of one private theta vertex must be on
opposite sides of its line rank; neither a third neighbor nor a
same-direction fork can be hidden by repeated sort labels. -/
theorem thetaPrivate_distinct_neighbor_directions
    (ws : List (PositiveWord S i j))
    (b : Fin ws.length)
    (p : wordInterior S (ws.get b))
    (y z : thetaVertices S ws)
    (hy : thetaAdjacent S ws (.inr ⟨b,p⟩) y)
    (hz : thetaAdjacent S ws (.inr ⟨b,p⟩) z)
    (hyz : y ≠ z) :
    ∃ q r : wordPositions S (ws.get b),
      y = thetaBranchPosition S ws b q ∧
      z = thetaBranchPosition S ws b r ∧
      ((wordPositionRank S (ws.get b) q =
           wordPositionRank S (ws.get b) p.val + 1 ∧
        wordPositionRank S (ws.get b) p.val =
           wordPositionRank S (ws.get b) r + 1) ∨
       (wordPositionRank S (ws.get b) p.val =
           wordPositionRank S (ws.get b) q + 1 ∧
        wordPositionRank S (ws.get b) r =
           wordPositionRank S (ws.get b) p.val + 1)) := by
  rcases thetaPrivate_neighbor_rank S ws b p y hy with ⟨q,hq,hu | hd⟩
  · rcases thetaPrivate_neighbor_rank S ws b p z hz with ⟨r,hr,hu' | hd'⟩
    · exfalso
      apply hyz
      exact private_neighbor_eq_of_same_rank S ws b hq hr
        (hu.trans hu'.symm)
    · exact ⟨q,r,hq,hr,Or.inl ⟨hu,hd'⟩⟩
  · rcases thetaPrivate_neighbor_rank S ws b p z hz with ⟨r,hr,hu' | hd'⟩
    · exact ⟨q,r,hq,hr,Or.inr ⟨hd,hu'⟩⟩
    · exfalso
      apply hyz
      apply private_neighbor_eq_of_same_rank S ws b hq hr
      omega

/-- An actual private point has at most two distinct neighbors.
This is the finite combinatorial degree bound used to force a
simple cycle to traverse whole private branches before switching. -/
theorem thetaPrivate_no_three_distinct_neighbors
    (ws : List (PositiveWord S i j))
    (b : Fin ws.length)
    (p : wordInterior S (ws.get b))
    (x y z : thetaVertices S ws)
    (hx : thetaAdjacent S ws (.inr ⟨b,p⟩) x)
    (hy : thetaAdjacent S ws (.inr ⟨b,p⟩) y)
    (hz : thetaAdjacent S ws (.inr ⟨b,p⟩) z)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    False := by
  obtain ⟨qx,qy,hqx,hqy,hup | hdown⟩ :=
    thetaPrivate_distinct_neighbor_directions S ws b p x y hx hy hxy
  · obtain ⟨hxUp,hyDown⟩ := hup
    obtain ⟨qy',qz,hqy',hqz,hup2 | hdown2⟩ :=
      thetaPrivate_distinct_neighbor_directions S ws b p y z hy hz hyz
    · obtain ⟨hyUp,hzDown⟩ := hup2
      omega
    · obtain ⟨hyDown',hzUp⟩ := hdown2
      have hRank : wordPositionRank S (ws.get b) qx =
          wordPositionRank S (ws.get b) qz := by omega
      exact hxz (private_neighbor_eq_of_same_rank S ws b hqx hqz hRank)
  · obtain ⟨hxDown,hyUp⟩ := hdown
    obtain ⟨qy',qz,hqy',hqz,hup2 | hdown2⟩ :=
      thetaPrivate_distinct_neighbor_directions S ws b p y z hy hz hyz
    · obtain ⟨hyUp',hzDown⟩ := hup2
      have hRank : wordPositionRank S (ws.get b) qx =
          wordPositionRank S (ws.get b) qz := by omega
      exact hxz (private_neighbor_eq_of_same_rank S ws b hqx hqz hRank)
    · obtain ⟨hyDown,hzUp⟩ := hdown2
      omega

end CCO.StrongExact
