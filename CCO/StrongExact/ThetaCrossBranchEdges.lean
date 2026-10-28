import CCO.StrongExact.ThetaNoRootArc

/-!
# C07: no theta edge belongs simultaneously to different private branches

If the embedded formal positions of two DIFFERENT long words
coincide, they must be literal shared roots. If both endpoints of
one of the words' diversity letters belong to another word's line,
that letter would directly connect the two global roots, which is
impossible because its word has length at least two.

These are purely finite formal-graph statements, independent of
source SAP/CCO and without an artificial equality edge.
-/

universe u v w

namespace CCO.StrongExact

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {i j : ι}

/-- A position on one branch identified with any formal position of
a DIFFERENT branch can be only its left or right endpoint. -/
theorem crossBranch_samePosition_isRoot
    (ws : List (PositiveWord S i j))
    (b c : Fin ws.length) (hbc : b ≠ c)
    (p : wordPositions S (ws.get b))
    (q : wordPositions S (ws.get c))
    (h : thetaBranchPosition S ws b p =
      thetaBranchPosition S ws c q) :
    p = wordSource S (ws.get b) ∨
    p = wordTarget S (ws.get b) := by
  by_cases hSource : p = wordSource S (ws.get b)
  · exact Or.inl hSource
  · by_cases hTarget : p = wordTarget S (ws.get b)
    · exact Or.inr hTarget
    · let p' : wordInterior S (ws.get b) :=
        ⟨p,hSource,hTarget⟩
      have hEq : b = c :=
        private_embedded_position_same_branch S ws b c p' q h
      exact (hbc hEq).elim

/-- If all words are genuinely long, an actual diversity LETTER
from branch b cannot have BOTH endpoints on a different branch c,
regardless of orientations and repeated named sorts. -/
theorem crossBranch_cannot_contain_edge
    (ws : List (PositiveWord S i j))
    (hLong : ∀ a : S.Atom i j,
      (PositiveWord.single a : PositiveWord S i j) ∉ ws)
    (b c : Fin ws.length) (hbc : b ≠ c)
    (e : wordEdgeIndex S (ws.get b))
    (p q : wordPositions S (ws.get c))
    (hSrc : thetaBranchEdgeSource S ws b e =
      thetaBranchPosition S ws c p)
    (hDst : thetaBranchEdgeTarget S ws b e =
      thetaBranchPosition S ws c q) : False := by
  have hSource :
      wordEdgeSource S (ws.get b) e =
        wordSource S (ws.get b) ∨
      wordEdgeSource S (ws.get b) e =
        wordTarget S (ws.get b) :=
    crossBranch_samePosition_isRoot S ws b c hbc
      (wordEdgeSource S (ws.get b) e) p hSrc
  have hTarget :
      wordEdgeTarget S (ws.get b) e =
        wordSource S (ws.get b) ∨
      wordEdgeTarget S (ws.get b) e =
        wordTarget S (ws.get b) :=
    crossBranch_samePosition_isRoot S ws b c hbc
      (wordEdgeTarget S (ws.get b) e) q hDst
  have hWordLong : ∀ a : S.Atom i j, ws.get b ≠ .single a := by
    intro a heq
    exact hLong a (by
      rw [← heq]
      exact List.get_mem ws b)
  have hImpossible :=
    wordEdge_no_root_pair_of_long S (ws.get b) hWordLong e
  rcases hSource with h0 | h1 <;>
    rcases hTarget with t0 | t1
  · exact (wordEdge_distinct S (ws.get b) e)
      (h0.trans t0.symm)
  · exact hImpossible (Or.inl ⟨h0,t1⟩)
  · exact hImpossible (Or.inr ⟨h1,t0⟩)
  · exact (wordEdge_distinct S (ws.get b) e)
      (h1.trans t1.symm)

/-- Distinct private branches cannot share even the same ordered
pair of formal edge endpoints. -/
theorem crossBranchEdge_no_parallel
    (ws : List (PositiveWord S i j))
    (hLong : ∀ a : S.Atom i j,
      (PositiveWord.single a : PositiveWord S i j) ∉ ws)
    (b c : Fin ws.length) (hbc : b ≠ c)
    (e : wordEdgeIndex S (ws.get b))
    (f : wordEdgeIndex S (ws.get c)) :
    ¬ (thetaBranchEdgeSource S ws b e =
         thetaBranchEdgeSource S ws c f ∧
       thetaBranchEdgeTarget S ws b e =
         thetaBranchEdgeTarget S ws c f) := by
  rintro ⟨hs,ht⟩
  exact crossBranch_cannot_contain_edge S ws hLong b c hbc e
    (wordEdgeSource S (ws.get c) f)
    (wordEdgeTarget S (ws.get c) f) hs ht

/-- Even reversed parallel edges between different private branches
cannot occur once every word has length at least two. -/
theorem crossBranchEdge_no_reversed_parallel
    (ws : List (PositiveWord S i j))
    (hLong : ∀ a : S.Atom i j,
      (PositiveWord.single a : PositiveWord S i j) ∉ ws)
    (b c : Fin ws.length) (hbc : b ≠ c)
    (e : wordEdgeIndex S (ws.get b))
    (f : wordEdgeIndex S (ws.get c)) :
    ¬ (thetaBranchEdgeSource S ws b e =
         thetaBranchEdgeTarget S ws c f ∧
       thetaBranchEdgeTarget S ws b e =
         thetaBranchEdgeSource S ws c f) := by
  rintro ⟨hs,ht⟩
  exact crossBranch_cannot_contain_edge S ws hLong b c hbc e
    (wordEdgeTarget S (ws.get c) f)
    (wordEdgeSource S (ws.get c) f) hs ht

end CCO.StrongExact
