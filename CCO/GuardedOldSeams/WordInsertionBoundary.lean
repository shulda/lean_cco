import CCO.GuardedOldSeams.Simultaneous
import Mathlib.Data.Fintype.Card

/-! The insertion theorem retains the whole original formal word.  Its
injectivity needs distinct real roots and enough vertices in the actual
complete member; a bounded finite diagnostic cannot erase these facts. -/

universe u v a

namespace CCO.GuardedOldSeams

open StrongExact

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,a} ι X)

theorem no_fresh_word_line_equal_roots {i : ι} (w : PositiveWord S i i)
    (x : X i) (Z : Set (Sigma X)) :
    ¬ Nonempty (FreshWordLine S w x x Z) := by
  rintro ⟨line⟩
  exact wordSource_ne_target S w (line.injective
    ((lineImage_source S line.toLiteralLine).trans
      (lineImage_target S line.toLiteralLine).symm))

/-- Every position of the specified original word consumes a distinct
point of the actual complete member containing that line. -/
theorem positions_card_le_complete_base {i j : ι} {w : PositiveWord S i j}
    {x : X i} {y : X j} {Z : Set (Sigma X)}
    (line : FreshWordLine S w x y Z) (B : FiniteInduced (X := X))
    (inside : lineRange S line.toLiteralLine ⊆ B.vertices)
    [Fintype (wordPositions S w)] [Fintype ↥B.vertices] :
    Fintype.card (wordPositions S w) ≤ Fintype.card ↥B.vertices := by
  let f : wordPositions S w → ↥B.vertices :=
    fun p => ⟨lineImage S line.toLiteralLine p, inside ⟨p, rfl⟩⟩
  apply Fintype.card_le_of_injective f
  intro p q hpq
  exact line.injective (congrArg (fun z : ↥B.vertices => z.val) hpq)

theorem no_whole_word_in_too_small_base {i j : ι} (w : PositiveWord S i j)
    (x : X i) (y : X j) (Z : Set (Sigma X)) (B : FiniteInduced (X := X))
    [Fintype (wordPositions S w)] [Fintype ↥B.vertices]
    (small : Fintype.card ↥B.vertices < Fintype.card (wordPositions S w)) :
    ¬ ∃ line : FreshWordLine S w x y Z,
      lineRange S line.toLiteralLine ⊆ B.vertices := by
  rintro ⟨line, inside⟩
  exact Nat.not_le_of_lt small (positions_card_le_complete_base S line B inside)

end CCO.GuardedOldSeams
