import CCO.StrongExact.ThetaCyclePrivateStep

/-!
# C07: any root-free finite stretch of a theta cycle stays in one branch

All edges between private vertices preserve the original word-occurrence
tag. Starting from a specific private vertex, a finite run of cycle
successors avoiding BOTH shared roots can therefore never switch
branches. This finite-interval lemma is a step toward classifying all
simple theta cycles as exactly two entire private words.
-/

universe u v w

namespace CCO.StrongExact

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {i j : ι}

/-- Repeated cyclic successor, with its original Fin index and no
choice of linear representative or endpoint outside the cycle. -/
def thetaCycleAdvance {n : Nat} (hn : 0 < n) (p : Fin n) :
    Nat → Fin n
  | 0 => p
  | k + 1 => cyclicNext hn (thetaCycleAdvance hn p k)

/-- A formal theta vertex avoiding both shared roots is a uniquely
branch-tagged private interior. The named endpoint sorts may coincide. -/
theorem thetaVertex_private_of_avoiding_roots
    (ws : List (PositiveWord S i j))
    (v : thetaVertices S ws)
    (hLeft : v ≠ thetaLeft S ws)
    (hRight : v ≠ thetaRight S ws) :
    ∃ b : Fin ws.length, ∃ t : wordInterior S (ws.get b),
      v = (.inr ⟨b,t⟩ : thetaVertices S ws) := by
  cases hv : v with
  | inl tag =>
      cases tag with
      | false =>
          exact False.elim (hLeft (by simpa only [thetaLeft] using hv))
      | true =>
          exact False.elim (hRight (by simpa only [thetaRight] using hv))
  | inr z =>
      cases z with
      | mk b t =>
          exact ⟨b,t,rfl⟩

/-- A run of cyclic successors that never hits either shared root
keeps the same original positive-word occurrence at every position.
This uses only the proved local private edge incidence. -/
theorem thetaCycle_rootfree_forward_same_branch
    (ws : List (PositiveWord S i j))
    (hLong : ∀ a : S.Atom i j,
      (PositiveWord.single a : PositiveWord S i j) ∉ ws)
    (C : SimpleCycle ((thetaEdgesOfLong S ws hLong).toDiagram))
    (start : Fin C.length) (b : Fin ws.length)
    (t : wordInterior S (ws.get b))
    (hStart : C.vertices start =
      (.inr ⟨b,t⟩ : thetaVertices S ws))
    (k : Nat)
    (hAvoid : ∀ m : Nat, m ≤ k →
      C.vertices (thetaCycleAdvance C.length_pos start m) ≠
          thetaLeft S ws ∧
      C.vertices (thetaCycleAdvance C.length_pos start m) ≠
          thetaRight S ws) :
    ∃ u : wordInterior S (ws.get b),
      C.vertices (thetaCycleAdvance C.length_pos start k) =
        (.inr ⟨b,u⟩ : thetaVertices S ws) := by
  induction k with
  | zero =>
      exact ⟨t, by simpa only [thetaCycleAdvance] using hStart⟩
  | succ k ih =>
      have hAvoidSmall : ∀ m : Nat, m ≤ k →
          C.vertices (thetaCycleAdvance C.length_pos start m) ≠
            thetaLeft S ws ∧
          C.vertices (thetaCycleAdvance C.length_pos start m) ≠
            thetaRight S ws := by
        intro m hm
        exact hAvoid m (by omega)
      obtain ⟨u,hu⟩ := ih hAvoidSmall
      obtain ⟨c,v,hv⟩ :=
        thetaVertex_private_of_avoiding_roots S ws
          (C.vertices (thetaCycleAdvance C.length_pos start (k+1)))
          (hAvoid (k+1) (by omega)).1
          (hAvoid (k+1) (by omega)).2
      have hstep : b = c :=
        thetaCycle_private_next_same_branch S ws hLong C
          (thetaCycleAdvance C.length_pos start k) b c u v
          hu (by simpa only [thetaCycleAdvance] using hv)
      cases hstep
      refine ⟨v, ?_⟩
      simpa only [thetaCycleAdvance] using hv

end CCO.StrongExact
