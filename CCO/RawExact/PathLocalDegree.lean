import CCO.RawExact.PrivateFanSimple

/-!
# B002 C12: degree-two geometry of genuine private RAW paths

Each positive-length reduced RAW word is a finite path. Its interior
position has exactly two distinct neighbours, the preceding and the
following position. This is the local combinatorial fact needed to
show that a simple fan cycle cannot leave a private path in its
interior, without assuming that a real walk is injective.

This is a statement about FORMAL positions; an actual WordPath may
still identify nonconsecutive real vertices.
-/

universe u v w

namespace CCO.RawExact

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)

/-- Every proper internal position has two genuinely distinct finite
neighbours, which exhaust all its private-path adjacency. -/
theorem pathInterior_exactly_two_neighbours {i j : ι}
    (word : RawWord S i j)
    (p : PathPosition S word)
    (hStart : 0 < p.val)
    (hFinish : p.val < diversityLength S word) :
    ∃ before after : PathPosition S word,
      before.val + 1 = p.val ∧
      after.val = p.val + 1 ∧
      before ≠ after ∧
      pathAdjacent S word before p ∧
      pathAdjacent S word p after ∧
      (∀ q : PathPosition S word,
        pathAdjacent S word p q →
          q = before ∨ q = after) := by
  let before : PathPosition S word :=
    ⟨p.val - 1, by omega⟩
  let after : PathPosition S word :=
    ⟨p.val + 1, by omega⟩
  refine ⟨before, after, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · dsimp [before]
    omega
  · dsimp [after]
    omega
  · intro hEq
    have hVal := congrArg Fin.val hEq
    dsimp [before, after] at hVal
    omega
  · change before.val + 1 = p.val ∨ p.val + 1 = before.val
    left
    dsimp [before]
    omega
  · change p.val + 1 = after.val ∨ after.val + 1 = p.val
    left
    dsimp [after]
  · intro q hAdj
    change p.val + 1 = q.val ∨ q.val + 1 = p.val at hAdj
    rcases hAdj with hPlus | hMinus
    · right
      apply Fin.ext
      dsimp [after]
      omega
    · left
      apply Fin.ext
      dsimp [before]
      omega

/-- Every private path edge is a step of exactly one unit in its
finite vertex index, in either direction. -/
theorem pathAdjacent_iff_step {i j : ι}
    (word : RawWord S i j)
    (p q : PathPosition S word) :
    pathAdjacent S word p q ↔
      p.val + 1 = q.val ∨ q.val + 1 = p.val :=
  Iff.rfl

end CCO.RawExact
