import CCO.StrongExact.ThetaCycleRootDistanceBounds
import CCO.StrongExact.ThetaCyclicIndexInverse
import CCO.StrongExact.ThetaCycleBranchSplit

/-!
# C07: the two global theta-cycle arcs use DIFFERENT private branches

At the common left root, its forward neighbor lies on the first
root-free arc, while its backward neighbor is the final private
vertex of the complementary arc. The two branch tags must differ
by the proved local root-degree/rank theorem. No word Helly, CCO or
SAP provider is used in this finite combinatorial argument.
-/

universe u v w
namespace CCO.StrongExact

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {i j : ι}

theorem thetaCycle_root_arcs_branch_tags_distinct
    (ws : List (PositiveWord S i j))
    (hLong : ∀ a : S.Atom i j,
      (PositiveWord.single a : PositiveWord S i j) ∉ ws)
    (C : SimpleCycle ((thetaEdgesOfLong S ws hLong).toDiagram))
    (p q : Fin C.length) (k l : Nat)
    (hp : C.vertices p = thetaLeft S ws)
    (hq : C.vertices q = thetaRight S ws)
    (hForwardEnd : thetaCycleAdvance C.length_pos p k = q)
    (hBackwardEnd : thetaCycleAdvance C.length_pos q l = p)
    (b c : Fin ws.length)
    (hForward : ∀ m : Nat, 0 < m → m < k →
      ∃ t : wordInterior S (ws.get b),
        C.vertices (thetaCycleAdvance C.length_pos p m) =
          (.inr ⟨b,t⟩ : thetaVertices S ws))
    (hBackward : ∀ m : Nat, 0 < m → m < l →
      ∃ t : wordInterior S (ws.get c),
        C.vertices (thetaCycleAdvance C.length_pos q m) =
          (.inr ⟨c,t⟩ : thetaVertices S ws)) :
    b ≠ c := by
  have hkTwo := thetaCycle_left_right_distance_ge_two
    S ws hLong C p q k hp hq hForwardEnd
  have hlTwo := thetaCycle_right_left_distance_ge_two
    S ws hLong C q p l hq hp hBackwardEnd
  obtain ⟨t,ht⟩ := hForward 1 (by omega) (by omega)
  obtain ⟨u,hu⟩ := hBackward (l - 1) (by omega) (by omega)
  have hNext : C.vertices (cyclicNext C.length_pos p) =
      (.inr ⟨b,t⟩ : thetaVertices S ws) := by
    simpa only [thetaCycleAdvance] using ht
  have hlStep : l - 1 + 1 = l := by omega
  have hNextIndex : cyclicNext C.length_pos
      (thetaCycleAdvance C.length_pos q (l - 1)) = p := by
    calc
      cyclicNext C.length_pos
        (thetaCycleAdvance C.length_pos q (l - 1)) =
        thetaCycleAdvance C.length_pos q ((l - 1) + 1) := rfl
      _ = thetaCycleAdvance C.length_pos q l := by rw [hlStep]
      _ = p := hBackwardEnd
  have hPrevIndex : thetaCycleAdvance C.length_pos q (l - 1) =
      cyclicPrev C.length_pos p := by
    calc
      thetaCycleAdvance C.length_pos q (l - 1) =
        cyclicPrev C.length_pos (cyclicNext C.length_pos
          (thetaCycleAdvance C.length_pos q (l - 1))) :=
            (cyclicPrev_next C.length_pos _).symm
      _ = cyclicPrev C.length_pos p :=
        congrArg (cyclicPrev C.length_pos) hNextIndex
  have hPrev : C.vertices (cyclicPrev C.length_pos p) =
      (.inr ⟨c,u⟩ : thetaVertices S ws) := by
    rw [hPrevIndex] at hu
    exact hu
  exact thetaCycle_left_neighbor_branches_distinct
    S ws hLong C p hp b c t u hNext hPrev

/-- Strong global structural decomposition into exactly TWO original
branch tags on the two strict root-to-root cycle arcs. The remaining
coverage of all private letter POSITIONS within those tags is separate. -/
theorem thetaCycle_two_arcs_distinct_branch_tags
    (ws : List (PositiveWord S i j))
    (hLong : ∀ a : S.Atom i j,
      (PositiveWord.single a : PositiveWord S i j) ∉ ws)
    (C : SimpleCycle ((thetaEdgesOfLong S ws hLong).toDiagram)) :
    ∃ p q : Fin C.length, ∃ k l : Nat,
      ∃ b c : Fin ws.length,
        b ≠ c ∧
        0 < k ∧ k < C.length ∧
        thetaCycleAdvance C.length_pos p k = q ∧
        l < C.length ∧
        thetaCycleAdvance C.length_pos q l = p ∧
        C.vertices p = thetaLeft S ws ∧
        C.vertices q = thetaRight S ws ∧
        (∀ m : Nat, 0 < m → m < k →
          ∃ t : wordInterior S (ws.get b),
            C.vertices (thetaCycleAdvance C.length_pos p m) =
              (.inr ⟨b,t⟩ : thetaVertices S ws)) ∧
        (∀ m : Nat, 0 < m → m < l →
          ∃ t : wordInterior S (ws.get c),
            C.vertices (thetaCycleAdvance C.length_pos q m) =
              (.inr ⟨c,t⟩ : thetaVertices S ws)) := by
  obtain ⟨p,q,k,l,b,c,hPositive,hk,hForwardEnd,hl,hBackwardEnd,
      hp,hq,hForward,hBackward⟩ :=
    thetaCycle_two_rootfree_arcs_have_branch_tags S ws hLong C
  have hDistinct := thetaCycle_root_arcs_branch_tags_distinct
    S ws hLong C p q k l hp hq hForwardEnd hBackwardEnd
    b c hForward hBackward
  exact ⟨p,q,k,l,b,c,hDistinct,hPositive,hk,hForwardEnd,hl,hBackwardEnd,
    hp,hq,hForward,hBackward⟩

end CCO.StrongExact
