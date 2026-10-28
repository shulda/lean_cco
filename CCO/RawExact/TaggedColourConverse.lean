import CCO.Finite

/-!
# B002 C12: actual typed converse of an old atomic pair-colour fingerprint

The full optional old-colour fingerprint is a DEPENDENT triple of
source sort, target sort, and genuine diversity atom (if any).
Its converse swaps the original sort indices and applies the actual
source's involutive converse to diversity atoms. Logical equality
remains `none`, never an invented diversity colour.

This allows arbitrary RAW walk-colour comparisons in the opposite
orientation without comparing abstract untyped colour tables.
-/

universe u v w

namespace CCO.RawExact

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)

/-- Converse of a FULL original typed, optional pair-colour
fingerprint, including the genuine logical diagonal. -/
def taggedColourConverse :
    (Σ i : ι, Σ j : ι, Option (S.Atom i j)) →
      (Σ i : ι, Σ j : ι, Option (S.Atom i j))
  | ⟨i,j,none⟩ => ⟨j,i,none⟩
  | ⟨i,j,some a⟩ => ⟨j,i,some (S.conv a)⟩

/-- Swapping two ACTUAL old points takes their correctly typed
full pair-colour fingerprint to its proper source converse. -/
theorem taggedColour_reverse_real (p q : Sigma X) :
    taggedColour S q p =
      taggedColourConverse S (taggedColour S p q) := by
  rcases p with ⟨i,x⟩
  rcases q with ⟨j,y⟩
  cases hc : S.colour x y with
  | none =>
      have hr : S.colour y x = none := by
        apply (S.colour_none_iff y x).mpr
        exact ((S.colour_none_iff x y).mp hc).symm
      simp [taggedColour, taggedColourConverse, hc, hr]
  | some a =>
      have hr : S.colour y x = some (S.conv a) :=
        (S.colour_swap x y a).mp hc
      simp [taggedColour, taggedColourConverse, hc, hr]

/-- Equality of forward full old pair-colour fingerprints implies
equality in the reverse orientation. This includes both diversity
atoms and actual logical equality, for repeated original sorts. -/
theorem taggedColour_reverse_eq_of_eq
    (p q p' q' : Sigma X)
    (h : taggedColour S p q = taggedColour S p' q') :
    taggedColour S q p = taggedColour S q' p' := by
  rw [taggedColour_reverse_real S p q,
    taggedColour_reverse_real S p' q', h]

end CCO.RawExact
