import CCO.StrongExact.ThetaVertices

/-!
# C07 private theta paths have genuine interior vertices

The single-letter path has exactly two formal positions, hence no
interior. Every cons word, regardless of repeated endpoint sorts,
has at least one private interior position: the source of its tail.
This is a literal formal-position statement, not an assumed real
injectivity or source atom realization.

It separates the easy direct-edge case from the hard CCO theta
case, where every profile word may be taken to have length at least two.
-/

universe u v w

namespace CCO.StrongExact

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u, v, w} ι X)
variable {i j k : ι}

/-- A one-letter positive path has no internal formal vertex. -/
theorem wordInterior_single_isEmpty (a : S.Atom i j) :
    IsEmpty (wordInterior S (.single a)) := by
  constructor
  intro p
  rcases p with ⟨b, hbS, hbT⟩
  cases b
  · exact hbS rfl
  · exact hbT rfl

/-- A positive word with at least two edges has a canonical genuinely
internal formal position (the source of its nonempty tail). -/
theorem wordInterior_cons_nonempty
    (a : S.Atom i j) (tail : PositiveWord S j k) :
    _root_.Nonempty (wordInterior S (.cons a tail)) := by
  let mid : wordPositions S (.cons a tail) :=
    some (wordSource S tail)
  have hSource : mid ≠ wordSource S (.cons a tail) := by
    intro h
    change some (wordSource S tail) = (none : Option (wordPositions S tail)) at h
    cases h
  have hTarget : mid ≠ wordTarget S (.cons a tail) := by
    intro h
    change some (wordSource S tail) = some (wordTarget S tail) at h
    exact (wordSource_ne_target S tail) (Option.some.inj h)
  exact ⟨⟨mid, hSource, hTarget⟩⟩

/-- Every nonsingleton positive word has an actual internal formal
position, without assuming anything about the original source age. -/
theorem wordInterior_nonempty_if_not_single
    (w : PositiveWord S i k)
    (hLong : ∀ a : S.Atom i k, w ≠ .single a) :
    _root_.Nonempty (wordInterior S w) := by
  cases w with
  | single a => exact False.elim ((hLong a) rfl)
  | cons a tail => exact wordInterior_cons_nonempty S a tail

end CCO.StrongExact
