import CCO.AutomaticEPCore.OriginalTypes
import CCO.ExactEPGeometry.OriginalOneSortDiversityRank

/-! B063 C26: actual one-original-sort exact quotients strictly reduce
ORIGINAL diversity rank. This is the existing source quotient application,
including finite/non-SAP quotients; no tower-length rank is substituted. -/

universe u v w r
namespace CCO.AutomaticEPCore
open CCO.APCharacter.Towers CCO.ExactEPGeometry
noncomputable section

/-- D01's actual old diversity count agrees with Nat.card of the finite
original palette, excluding its separate logical diagonal. -/
theorem originalDiversityRank_eq_natCard (A : CurrentSource.{u,v,w,r}) (base : A.Sorts) :
    originalDiversityRank A base = Nat.card (A.source.Atom base base) := by
  letI := A.source.finiteAtom base base
  exact Nat.card_eq_fintype_card.symm

/-- C26 at the literal original canonical quotient palette. Every quotient
action/orbital/presentation clause is discharged by the accepted source
instance. A proper original FULL EXACT kernel, not a supplied drop lemma,
is the sole strictness input. -/
theorem original_exact_quotient_rank_lt
    (A : CurrentSource.{u,v,w,r}) (base : A.Sorts)
    (hOne : ∀ i : A.Sorts, base = i)
    (E : ExactEq A.source base) (hE : (⊥ : ExactEq A.source base) < E) :
    let J := originalExactSourceKernelFamily A base hOne E
    let W := originalExactSourceKernelWords A base hOne E
    let hW := originalExactSourceKernelWords_relation A base hOne E
    let Q := CCO.ExactCRT.CanonicalTyped.source A.source A.homogeneous J W hW
    Nat.card (Q.Atom base base) < originalDiversityRank A base := by
  rw [originalDiversityRank_eq_natCard]
  exact originalOneSortExactQuotientDiversityRank_strict A base hOne E hE

end
end CCO.AutomaticEPCore
