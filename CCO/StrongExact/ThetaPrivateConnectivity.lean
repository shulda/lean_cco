import CCO.StrongExact.ThetaAdjacency

/-!
# C07: private theta vertices cannot travel between word occurrences

Remove the two common formal roots from the hard theta graph. The
remaining induced graph is a disjoint union of private word lines:
every adjacent pair and every finite private walk preserve the
literal word-occurrence tag. This is a connectivity invariant, not
an assumed complete cycle classification.
-/

universe u v w

namespace CCO.StrongExact

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {i j : ι}

/-- The private, non-root formal vertices, retaining each branch tag. -/
abbrev PrivateThetaVertex (ws : List (PositiveWord S i j)) :=
  Σ b : Fin ws.length, wordInterior S (ws.get b)

/-- An adjacency between private formal vertices can never change the
index of the original positive word occurrence. -/
theorem privateTheta_adj_same_branch
    (ws : List (PositiveWord S i j))
    (x y : PrivateThetaVertex S ws)
    (h : thetaAdjacent S ws (.inr x) (.inr y)) :
    x.1 = y.1 := by
  rcases x with ⟨b,p⟩
  rcases y with ⟨c,q⟩
  change b = c
  by_contra hne
  apply thetaAdjacent_no_cross_private S ws b c hne p q
  rw [thetaBranchPosition_interior S ws b p,
      thetaBranchPosition_interior S ws c q]
  exact h

/-- Genuine finite walks in the induced graph on private vertices.
Only actual old diversity adjacency steps are permitted. -/
inductive PrivateThetaWalk (ws : List (PositiveWord S i j)) :
    PrivateThetaVertex S ws → PrivateThetaVertex S ws → Prop where
  | refl (x : PrivateThetaVertex S ws) : PrivateThetaWalk ws x x
  | step {x y z : PrivateThetaVertex S ws}
      (hxy : thetaAdjacent S ws (.inr x) (.inr y))
      (hyz : PrivateThetaWalk ws y z) : PrivateThetaWalk ws x z

/-- Every connected private walk stays in the SAME word occurrence;
branch changes are possible only at the two shared formal roots. -/
theorem privateTheta_walk_same_branch
    (ws : List (PositiveWord S i j))
    {x y : PrivateThetaVertex S ws}
    (h : PrivateThetaWalk S ws x y) : x.1 = y.1 := by
  induction h with
  | refl _ => rfl
  | @step x y z hxy hyz ih =>
      exact (privateTheta_adj_same_branch S ws x y hxy).trans ih

end CCO.StrongExact
