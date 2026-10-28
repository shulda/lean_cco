import CCO.StrongExact.ThetaCycleFirstArc

/-!
# C07: the complementary root-free cyclic arc also uses one branch

The interval from the right theta root forward to the left root
has the same exact finite index and private-branch properties as
the left-to-right arc. Root labels and original named sorts are
not identified; the statement works with repeated sort tags.
-/

universe u v w
namespace CCO.StrongExact

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {i j : ι}

/-- Neither formal root can occur strictly inside a finite forward
right-to-left root arc on a genuine hard-theta simple cycle. -/
theorem thetaCycle_reverse_between_roots_avoids_roots
    (ws : List (PositiveWord S i j))
    (hLong : ∀ a : S.Atom i j,
      (PositiveWord.single a : PositiveWord S i j) ∉ ws)
    (C : SimpleCycle ((thetaEdgesOfLong S ws hLong).toDiagram))
    (q p : Fin C.length) (k m : Nat)
    (hq : C.vertices q = thetaRight S ws)
    (hp : C.vertices p = thetaLeft S ws)
    (hk : k < C.length)
    (hReached : thetaCycleAdvance C.length_pos q k = p)
    (hm : 0 < m) (hmk : m < k) :
    C.vertices (thetaCycleAdvance C.length_pos q m) ≠
        thetaLeft S ws ∧
    C.vertices (thetaCycleAdvance C.length_pos q m) ≠
        thetaRight S ws := by
  constructor
  · intro h
    have hIndex : thetaCycleAdvance C.length_pos q m = p :=
      C.vertices.injective (h.trans hp.symm)
    have hmk := thetaCycleAdvance_injective_lt
      C.length_pos q m k (by omega) hk
      (hIndex.trans hReached.symm)
    omega
  · intro h
    have hIndex : thetaCycleAdvance C.length_pos q m = q :=
      C.vertices.injective (h.trans hq.symm)
    have hEq : thetaCycleAdvance C.length_pos q m =
        thetaCycleAdvance C.length_pos q 0 := by
      simpa only [thetaCycleAdvance] using hIndex
    have hmzero := thetaCycleAdvance_injective_lt
      C.length_pos q m 0 (by omega) C.length_pos hEq
    omega

/-- The whole strict forward arc from right root to left root has
one original word-occurrence tag, without a global cycle theorem. -/
theorem thetaCycle_right_to_left_arc_branch
    (ws : List (PositiveWord S i j))
    (hLong : ∀ a : S.Atom i j,
      (PositiveWord.single a : PositiveWord S i j) ∉ ws)
    (C : SimpleCycle ((thetaEdgesOfLong S ws hLong).toDiagram))
    (q p : Fin C.length) (k : Nat)
    (hq : C.vertices q = thetaRight S ws)
    (hp : C.vertices p = thetaLeft S ws)
    (hk : k < C.length)
    (hReached : thetaCycleAdvance C.length_pos q k = p) :
    ∃ b : Fin ws.length,
      ∀ m : Nat, 0 < m → m < k →
        ∃ t : wordInterior S (ws.get b),
          C.vertices (thetaCycleAdvance C.length_pos q m) =
            (.inr ⟨b,t⟩ : thetaVertices S ws) := by
  obtain ⟨b,t,hStart⟩ :=
    thetaCycle_right_next_private S ws hLong C q hq
  refine ⟨b, ?_⟩
  intro m hm hmk
  let r : Nat := m - 1
  have hrm : r + 1 = m := by
    dsimp only [r]
    omega
  have hAvoid (s : Nat) (hs : s ≤ r) :
      C.vertices (thetaCycleAdvance C.length_pos
        (cyclicNext C.length_pos q) s) ≠ thetaLeft S ws ∧
      C.vertices (thetaCycleAdvance C.length_pos
        (cyclicNext C.length_pos q) s) ≠ thetaRight S ws := by
    have hPos : 0 < s + 1 := by omega
    have hLess : s + 1 < k := by omega
    have hNo := thetaCycle_reverse_between_roots_avoids_roots S ws hLong
      C q p k (s + 1) hq hp hk hReached hPos hLess
    simpa only [thetaCycleAdvance_from_next] using hNo
  obtain ⟨u,hu⟩ := thetaCycle_rootfree_forward_same_branch
    S ws hLong C (cyclicNext C.length_pos q) b t hStart r hAvoid
  have hIndex : thetaCycleAdvance C.length_pos
      (cyclicNext C.length_pos q) r =
      thetaCycleAdvance C.length_pos q m := by
    rw [thetaCycleAdvance_from_next, hrm]
  rw [hIndex] at hu
  exact ⟨u,hu⟩

end CCO.StrongExact
