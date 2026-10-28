import CCO.StrongExact.ThetaCycleSecondArc

/-!
# C07: the two root-to-root cyclic arcs each have one private branch

For any actual specified simple hard-theta cycle, choose its distinct
shared roots and the finite forward successor distances in both
directions. All private vertices strictly between the roots in each
direction belong to one original word-occurrence tag, possibly different
between the two arcs. This theorem does NOT assert that either arc
has yet been proved to exhaust all the positions of its word, nor
does it posit a missing CCO/Helly provider.
-/

universe u v w
namespace CCO.StrongExact

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {i j : ι}

theorem thetaCycle_two_rootfree_arcs_have_branch_tags
    (ws : List (PositiveWord S i j))
    (hLong : ∀ a : S.Atom i j,
      (PositiveWord.single a : PositiveWord S i j) ∉ ws)
    (C : SimpleCycle ((thetaEdgesOfLong S ws hLong).toDiagram)) :
    ∃ p q : Fin C.length, ∃ k l : Nat,
      ∃ b c : Fin ws.length,
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
  obtain ⟨p,q,k,hPositive,hk,hReached,hp,hq⟩ :=
    thetaCycle_roots_have_forward_distance S ws hLong C
  obtain ⟨l,hl,hBack⟩ :=
    thetaCycleAdvance_reaches C.length_pos q p
  obtain ⟨b,hFront⟩ :=
    thetaCycle_left_to_right_arc_branch S ws hLong C
      p q k hp hq hk hReached
  obtain ⟨c,hReverse⟩ :=
    thetaCycle_right_to_left_arc_branch S ws hLong C
      q p l hq hp hl hBack
  exact ⟨p,q,k,l,b,c,hPositive,hk,hReached,hl,hBack,
    hp,hq,hFront,hReverse⟩

end CCO.StrongExact
