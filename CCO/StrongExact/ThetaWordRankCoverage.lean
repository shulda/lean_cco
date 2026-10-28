import CCO.StrongExact.ThetaExceptLeftRank
import CCO.StrongExact.ThetaLineEdges

/-!
# C07: a positive word's finite rank covers every integer in its range

The original word positions and literal diversity-letter indices
are linearly ranked without gaps. Each integer from zero through the
terminal rank is attained by exactly one formal vertex; each integer
strictly below the terminal rank is the source rank of a literal
diversity letter. This holds for arbitrary repeated original sorts
and needs no source homogeneity, SAP, CCO or identity atom.
-/

universe u v w

namespace CCO.StrongExact

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)

/-- All word line ranks between zero and the final target rank
are realized by literal positions of the *same* positive word. -/
theorem wordPositionRank_exists
    {i j : ι} (word : PositiveWord S i j) :
    ∀ n : Nat,
      n ≤ wordPositionRank S word (wordTarget S word) →
      ∃ p : wordPositions S word,
        wordPositionRank S word p = n := by
  induction word with
  | single a =>
      intro n hn
      change n ≤ 1 at hn
      by_cases hzero : n = 0
      · refine ⟨false, ?_⟩
        simp [wordPositionRank, hzero]
      · have hone : n = 1 := by omega
        refine ⟨true, ?_⟩
        simp [wordPositionRank, hone]
  | cons a tail ih =>
      intro n hn
      change n ≤ 1 + wordPositionRank S tail
        (wordTarget S tail) at hn
      by_cases hzero : n = 0
      · refine ⟨none, ?_⟩
        simp [wordPositionRank, hzero]
      · have htail : n - 1 ≤ wordPositionRank S tail
            (wordTarget S tail) := by omega
        obtain ⟨p, hp⟩ := ih (n - 1) htail
        refine ⟨some p, ?_⟩
        change 1 + wordPositionRank S tail p = n
        rw [hp]
        omega

/-- Each original letter rank appears as the source of one ACTUAL
diversity word edge; there is no missing edge or inserted equality. -/
theorem wordEdgeSourceRank_exists
    {i j : ι} (word : PositiveWord S i j) :
    ∀ n : Nat,
      n < wordPositionRank S word (wordTarget S word) →
      ∃ e : wordEdgeIndex S word,
        wordPositionRank S word (wordEdgeSource S word e) = n := by
  induction word with
  | single a =>
      intro n hn
      change n < 1 at hn
      have hzero : n = 0 := by omega
      refine ⟨PUnit.unit, ?_⟩
      simp [wordPositionRank, wordEdgeSource, hzero]
  | cons a tail ih =>
      intro n hn
      change n < 1 + wordPositionRank S tail
        (wordTarget S tail) at hn
      by_cases hzero : n = 0
      · refine ⟨.inl PUnit.unit, ?_⟩
        simp [wordPositionRank, wordEdgeSource, hzero]
      · have htail : n - 1 <
            wordPositionRank S tail (wordTarget S tail) := by omega
        obtain ⟨e, he⟩ := ih (n - 1) htail
        refine ⟨.inr e, ?_⟩
        change 1 + wordPositionRank S tail
          (wordEdgeSource S tail e) = n
        rw [he]
        omega

end CCO.StrongExact
