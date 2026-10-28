import CCO.StrongExact.ThetaArcWitness
import CCO.StrongExact.ThetaLongEdges

/-!
# C07: hard theta diagrams have no direct root-to-root candidate edge

Every genuinely long positive word has at least two letters. Its
literal edge-rank increases by exactly one per letter, whereas
the two formal roots differ in rank by at least two. Thus no
forward *or reversed* word letter directly joins them.

The all-branch theorem uses the proven private-branch injection and
the exhaustive theta candidate arc witness. It does not assume
WordHelly, a new source axiom, or any SAP/CCO consequence.
-/

universe u v w

namespace CCO.StrongExact

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {i j : ι}

/-- A genuine letter can never go BACKWARDS from the last formal
word position to the first, regardless of word length. -/
theorem wordEdge_not_backward
    (word : PositiveWord S i j) (e : wordEdgeIndex S word) :
    ¬ (wordEdgeSource S word e = wordTarget S word ∧
       wordEdgeTarget S word e = wordSource S word) := by
  rintro ⟨hSource,hTarget⟩
  have hStep := wordEdge_rank_step S word e
  rw [hSource, hTarget, wordSource_rank_zero S word] at hStep
  have hPos := wordTarget_rank_positive S word
  omega

/-- No atomic letter of a word of length >= 2 joins its global
endpoints in either orientation. The endpoints can share a named SORT. -/
theorem wordEdge_no_root_pair_of_long
    (word : PositiveWord S i j)
    (hLong : ∀ a : S.Atom i j, word ≠ .single a)
    (e : wordEdgeIndex S word) :
    ¬ ((wordEdgeSource S word e = wordSource S word ∧
         wordEdgeTarget S word e = wordTarget S word) ∨
       (wordEdgeSource S word e = wordTarget S word ∧
         wordEdgeTarget S word e = wordSource S word)) := by
  intro h
  rcases h with hForward | hBackward
  · cases word with
    | single a => exact (hLong a rfl).elim
    | cons a tail =>
        exact no_direct_letter_in_long_word S a tail e hForward
  · exact wordEdge_not_backward S word e hBackward

/-- If one private literal word letter joins BOTH shared theta roots,
then its original word edge joins BOTH original word endpoints. -/
private theorem thetaBranchEdge_no_root_pair
    (ws : List (PositiveWord S i j)) (b : Fin ws.length)
    (hLong : ∀ a : S.Atom i j,
       (PositiveWord.single a : PositiveWord S i j) ∉ ws)
    (e : wordEdgeIndex S (ws.get b)) :
    ¬ ((thetaBranchEdgeSource S ws b e = thetaLeft S ws ∧
         thetaBranchEdgeTarget S ws b e = thetaRight S ws) ∨
       (thetaBranchEdgeSource S ws b e = thetaRight S ws ∧
         thetaBranchEdgeTarget S ws b e = thetaLeft S ws)) := by
  have hNo : ∀ a : S.Atom i j, (ws.get b) ≠ .single a := by
    intro a heq
    exact hLong a (by
      rw [← heq]
      exact List.get_mem ws b)
  have hLetter := wordEdge_no_root_pair_of_long S (ws.get b) hNo e
  have hInj := thetaBranchPosition_injective S ws b
  have hFromLeft (p : wordPositions S (ws.get b))
      (hp : thetaBranchPosition S ws b p = thetaLeft S ws) :
      p = wordSource S (ws.get b) :=
    hInj (hp.trans (thetaBranchPosition_source S ws b).symm)
  have hFromRight (p : wordPositions S (ws.get b))
      (hp : thetaBranchPosition S ws b p = thetaRight S ws) :
      p = wordTarget S (ws.get b) :=
    hInj (hp.trans (thetaBranchPosition_target S ws b).symm)
  intro h
  apply hLetter
  rcases h with ⟨hs,ht⟩ | ⟨hs,ht⟩
  · exact Or.inl ⟨hFromLeft _ hs, hFromRight _ ht⟩
  · exact Or.inr ⟨hFromRight _ hs, hFromLeft _ ht⟩

/-- Hard theta candidate edges have no root-to-root arc in EITHER
direction, even when the two roots have identical named sorts. -/
theorem thetaArcs_no_root_pair
    (ws : List (PositiveWord S i j))
    (hLong : ∀ a : S.Atom i j,
       (PositiveWord.single a : PositiveWord S i j) ∉ ws)
    (arc : ThetaArc S ws) (hArc : arc ∈ thetaArcs S ws) :
    ¬ ((arc.src = thetaLeft S ws ∧ arc.dst = thetaRight S ws) ∨
       (arc.src = thetaRight S ws ∧ arc.dst = thetaLeft S ws)) := by
  obtain ⟨b,e,⟨hs,ht⟩ | ⟨hs,ht⟩⟩ :=
    thetaArc_endpoints_on_branch S ws arc hArc
  · intro h
    apply thetaBranchEdge_no_root_pair S ws b hLong e
    rcases h with ⟨hsl,htr⟩ | ⟨hsr,htl⟩
    · exact Or.inl ⟨hs.symm.trans hsl, ht.symm.trans htr⟩
    · exact Or.inr ⟨hs.symm.trans hsr, ht.symm.trans htl⟩
  · intro h
    apply thetaBranchEdge_no_root_pair S ws b hLong e
    rcases h with ⟨hsl,htr⟩ | ⟨hsr,htl⟩
    · exact Or.inr ⟨ht.symm.trans htr, hs.symm.trans hsl⟩
    · exact Or.inl ⟨ht.symm.trans htl, hs.symm.trans hsr⟩

end CCO.StrongExact
