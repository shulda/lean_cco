import CCO.AutomaticEPCore.OriginalTypes

/-! B063 C28: the original-rank-zero base is an actual singleton carrier,
and a literal unary refinement of that carrier has at most one realized
label. No infinite-source or zero-coordinate MI chart is assumed. -/

universe u v w r
namespace CCO.AutomaticEPCore
open CCO.APCharacter.Towers CCO.ParityHasse.Original
noncomputable section

/-- Zero ORIGINAL diversity rank forces at most one actual old point. -/
theorem original_rank_zero_subsingleton
    (A : CurrentSource.{u,v,w,r}) (base : A.Sorts)
    (hOne : ∀ i : A.Sorts, base = i)
    (rank_zero : originalDiversityRank A base = 0) :
    Subsingleton (Sigma A.Point) := by
  letI := A.source.finiteAtom base base
  change Fintype.card (A.source.Atom base base) = 0 at rank_zero
  letI : IsEmpty (A.source.Atom base base) := Fintype.card_eq_zero_iff.mp rank_zero
  refine ⟨?_⟩
  rintro ⟨i,x⟩ ⟨j,y⟩
  cases hOne i
  cases hOne j
  cases hc : A.source.colour x y with
  | none => exact (A.source.colour_none_iff x y).mp hc
  | some a => exact isEmptyElim a

/-- Every current label is realized, so the global old-carrier bijection
prevents a rank-zero original point from splitting into different labels. -/
theorem rank_zero_realized_types_unique
    (A B : CurrentSource.{u,v,w,r}) (P : UnaryReduct A.source B.source)
    (base : A.Sorts) (hOne : ∀ i : A.Sorts, base = i)
    (rank_zero : originalDiversityRank A base = 0) (s t : B.Sorts) : s = t := by
  letI := original_rank_zero_subsingleton A base hOne rank_zero
  obtain ⟨x⟩ := B.source.nonemptySort s
  obtain ⟨y⟩ := B.source.nonemptySort t
  exact congrArg Sigma.fst (P.bijective.1
    (Subsingleton.elim (P.project ⟨s,x⟩) (P.project ⟨t,y⟩)))

end
end CCO.AutomaticEPCore
