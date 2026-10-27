import CCO.StrongExact.ThetaLineEdges

/-!
# C07 private paths have a strict finite linear rank

For every genuinely positive typed diversity word, give each formal
position its integer distance from the first root. The first vertex
has rank zero and every literal diversity letter increases rank by
exactly one. Thus no oriented path-edge can point backwards or be
a loop, independently of repeated sort tags.

This is a concrete combinatorial invariant needed to show that a
simple cycle through the full internally disjoint theta graph
traverses two WHOLE private branches, not arbitrary fragments.
No SAP, semantic CCO, NR2 or equality pseudoletter is assumed here.
-/

universe u v w

namespace CCO.StrongExact

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)

/-- Literal edge-distance from the first formal root. -/
def wordPositionRank {i j : ι} :
    (word : PositiveWord S i j) →
      wordPositions S word → Nat
  | .single _, p => cond p 1 0
  | .cons _ tail, p =>
      match p with
      | none => 0
      | some q => 1 + wordPositionRank tail q

theorem wordSource_rank_zero {i j : ι}
    (word : PositiveWord S i j) :
    wordPositionRank S word (wordSource S word) = 0 := by
  cases word <;> rfl

/-- Every actual old diversity LETTER, including repeated-sort
steps, advances the formal position rank by exactly one. -/
theorem wordEdge_rank_step {i j : ι}
    (word : PositiveWord S i j)
    (e : wordEdgeIndex S word) :
    wordPositionRank S word (wordEdgeTarget S word e) =
      wordPositionRank S word (wordEdgeSource S word e) + 1 := by
  induction word with
  | single a =>
      cases e
      rfl
  | cons a tail ih =>
      cases e with
      | inl _ =>
          rfl
      | inr e =>
          change 1 + wordPositionRank S tail
            (wordEdgeTarget S tail e) =
            (1 + wordPositionRank S tail
              (wordEdgeSource S tail e)) + 1
          omega

/-- A literal positive word edge is strictly forward in the ranked
formal path. This already rules out self-loops and reversed duplicates
within an individual branch. -/
theorem wordEdge_rank_strict {i j : ι}
    (word : PositiveWord S i j)
    (e : wordEdgeIndex S word) :
    wordPositionRank S word (wordEdgeSource S word e) <
      wordPositionRank S word (wordEdgeTarget S word e) := by
  rw [wordEdge_rank_step S word e]
  omega


/-- Every formal position of a positive word has a UNIQUE rank,
so a positive word really is a line, not a collection of branches.
This is purely combinatorial and independent of its atomic colours. -/
theorem wordPositionRank_injective {i j : ι}
    (word : PositiveWord S i j) :
    Function.Injective (wordPositionRank S word) := by
  induction word with
  | single a =>
      intro p q h
      cases p <;> cases q <;> simp_all [wordPositionRank]
  | cons a tail ih =>
      intro p q h
      cases p with
      | none =>
          cases q with
          | none => rfl
          | some q =>
              change 0 = 1 + wordPositionRank S tail q at h
              omega
      | some p =>
          cases q with
          | none =>
              change 1 + wordPositionRank S tail p = 0 at h
              omega
          | some q =>
              have hRank : wordPositionRank S tail p =
                  wordPositionRank S tail q := by
                change 1 + wordPositionRank S tail p =
                  1 + wordPositionRank S tail q at h
                omega
              exact congrArg Option.some (ih hRank)

/-- A positive word has at most one directed outgoing diversity
edge from each formal vertex. This is the key linear-branch invariant
for proving single-valued theta edge colours. -/
theorem wordEdgeSource_injective {i j : ι}
    (word : PositiveWord S i j) :
    Function.Injective (wordEdgeSource S word) := by
  induction word with
  | single a =>
      intro e e' h
      cases e
      cases e'
      rfl
  | cons a tail ih =>
      intro e e' h
      cases e with
      | inl x =>
          cases e' with
          | inl y =>
              cases x
              cases y
              rfl
          | inr y =>
              change (none : Option (wordPositions S tail)) =
                some (wordEdgeSource S tail y) at h
              cases h
      | inr x =>
          cases e' with
          | inl y =>
              change some (wordEdgeSource S tail x) =
                (none : Option (wordPositions S tail)) at h
              cases h
          | inr y =>
              change some (wordEdgeSource S tail x) =
                some (wordEdgeSource S tail y) at h
              exact congrArg Sum.inr (ih (Option.some.inj h))

end CCO.StrongExact
