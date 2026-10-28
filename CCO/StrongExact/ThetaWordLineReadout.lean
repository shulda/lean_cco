import CCO.StrongExact.ThetaLineEdges
import CCO.PositiveWords

/-!
# C07: read a represented positive word from a literally realised line

A family of actual original-sort points indexed by the finite formal
positions of a positive word determines a genuine represented walk
when every single typed diversity letter occurs on its prescribed
successive pair of points. The proof is a dependent induction through
the actual intermediate named sorts, without asserting injectivity or
using any artificial strong identity.
-/

universe u v w

namespace CCO.StrongExact

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)

/-- Every finite real point sequence respecting all actual original
diversity letters is a witness of the equality-inclusive represented
word relation at its two literal real terminals. The word itself is
positive: there are no identity letters in its input or output. -/
theorem represented_of_literal_word_line {i j : ι}
    (w : PositiveWord S i j) :
    ∀ (point : ∀ p : wordPositions S w,
        X (wordPositionSort S w p)),
      (∀ e : wordEdgeIndex S w,
        S.colour (point (wordEdgeSource S w e))
          (point (wordEdgeTarget S w e)) =
          some (wordEdgeAtom S w e)) →
      PositiveWord.represented S w
        ((wordSource_sort S w) ▸ point (wordSource S w))
        ((wordTarget_sort S w) ▸ point (wordTarget S w)) := by
  induction w with
  | single a =>
      intro point hedges
      change S.colour (point false) (point true) = some a
      exact hedges PUnit.unit
  | cons a tail ih =>
      intro point hedges
      let tailPoint : ∀ q : wordPositions S tail,
          X (wordPositionSort S tail q) :=
        fun q => point (some q)
      have hTailEdges :
          ∀ e : wordEdgeIndex S tail,
          S.colour (tailPoint (wordEdgeSource S tail e))
            (tailPoint (wordEdgeTarget S tail e)) =
            some (wordEdgeAtom S tail e) := by
        intro e
        exact hedges (.inr e)
      have hTail := ih tailPoint hTailEdges
      let mid : X _ :=
        (wordSource_sort S tail) ▸ tailPoint (wordSource S tail)
      have hFirst : S.colour (point none) mid = some a := by
        have h := hedges (.inl PUnit.unit)
        simpa [mid, tailPoint, wordEdgeSource,
          wordEdgeTarget, wordEdgeAtom] using h
      change ∃ y : X _, S.colour (point none) y = some a ∧
        PositiveWord.represented S tail y
          ((wordTarget_sort S tail) ▸ tailPoint (wordTarget S tail))
      exact ⟨mid, hFirst, hTail⟩

end CCO.StrongExact
