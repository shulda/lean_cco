import CCO.StrongExact.ThetaCycleRootDistance
import CCO.StrongExact.ThetaCycleAdvanceShift

/-!
# C07: a whole root-free cyclic arc uses one original private branch

Choose the unique finite forward distance k from the left root
to the right root on a simple hard-theta cycle. All strict
intermediate cyclic indices avoid both roots; by the finite
root-free branch-invariance theorem they belong to ONE original
positive-word occurrence. This does not yet prove that the
positions exhaust every letter of that word.
-/

universe u v w
namespace CCO.StrongExact

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {i j : ι}

theorem thetaCycle_left_to_right_arc_branch
    (ws : List (PositiveWord S i j))
    (hLong : ∀ a : S.Atom i j,
      (PositiveWord.single a : PositiveWord S i j) ∉ ws)
    (C : SimpleCycle ((thetaEdgesOfLong S ws hLong).toDiagram))
    (p q : Fin C.length) (k : Nat)
    (hp : C.vertices p = thetaLeft S ws)
    (hq : C.vertices q = thetaRight S ws)
    (hk : k < C.length)
    (hReached : thetaCycleAdvance C.length_pos p k = q) :
    ∃ b : Fin ws.length,
      ∀ m : Nat, 0 < m → m < k →
        ∃ t : wordInterior S (ws.get b),
          C.vertices (thetaCycleAdvance C.length_pos p m) =
            (.inr ⟨b,t⟩ : thetaVertices S ws) := by
  obtain ⟨b,t,hStart⟩ :=
    thetaCycle_left_next_private S ws hLong C p hp
  refine ⟨b, ?_⟩
  intro m hm hmk
  let r : Nat := m - 1
  have hrm : r + 1 = m := by
    dsimp only [r]
    omega
  have hAvoid (s : Nat) (hs : s ≤ r) :
      C.vertices (thetaCycleAdvance C.length_pos
        (cyclicNext C.length_pos p) s) ≠ thetaLeft S ws ∧
      C.vertices (thetaCycleAdvance C.length_pos
        (cyclicNext C.length_pos p) s) ≠ thetaRight S ws := by
    have hPos : 0 < s + 1 := by omega
    have hLess : s + 1 < k := by omega
    have hNo := thetaCycle_between_roots_avoids_roots S ws hLong
      C p q k (s + 1) hp hq hk hReached hPos hLess
    simpa only [thetaCycleAdvance_from_next] using hNo
  obtain ⟨u,hu⟩ := thetaCycle_rootfree_forward_same_branch
    S ws hLong C (cyclicNext C.length_pos p) b t hStart r hAvoid
  have hIndex : thetaCycleAdvance C.length_pos
      (cyclicNext C.length_pos p) r =
      thetaCycleAdvance C.length_pos p m := by
    rw [thetaCycleAdvance_from_next, hrm]
  rw [hIndex] at hu
  exact ⟨u,hu⟩

end CCO.StrongExact
