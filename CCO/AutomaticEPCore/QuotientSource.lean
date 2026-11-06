import CCO.AutomaticEPCore.SourceQuotientLift
import CCO.AutomaticEPCore.QuotientRank
import CCO.SimultaneousQuotients.Exports
import CCO.ExactEPGeometry.OriginalAllCurrentQuotientSource
import CCO.ExactEPGeometry.OriginalOccupancyQuotientSource

/-! The source to which the outer ORIGINAL diversity induction applies
is an actual CurrentSource on literal original E-classes. All AP/HOM-CCO
and countability duties are discharged by the accepted exact-quotient
source theorem, also when the quotient is finite and fails SAP. -/

universe u v w t
namespace CCO.AutomaticEPCore
open CCO.APCharacter.Towers CCO.ExactEPGeometry
open CCO.SimultaneousQuotients
noncomputable section

def originalCoreQuotientCurrentSource
    (A : CurrentSource.{u,v,w,t}) (base : A.Sorts)
    (hOne : ∀ i : A.Sorts, base = i) (E : ExactEq A.source base) :
    CurrentSource.{u,v,v,t} := by
  let J := originalExactSourceKernelFamily A base hOne E
  let W := originalExactSourceKernelWords A base hOne E
  let hW := originalExactSourceKernelWords_relation A base hOne E
  letI : ∀ i, Countable (A.Point i) := A.countable
  let properties : SourceProperties.{u,v,w,t,max u v}
      A.source A.homogeneous J W hW :=
    simultaneous_exact_quotients A.source A.homogeneous J W hW A.cco
  exact {
    Sorts := A.Sorts
    Point := fun i => Quotient (J i)
    source := originalCoreQuotient A base hOne E
    G := A.G
    group := inferInstance
    action := action A.source A.homogeneous J W hW
    homogeneous := properties.homogeneous
    countable := fun i => countable_carrier J i
    cco := properties.cycles }

theorem originalCoreQuotientCurrentSource_source
    (A : CurrentSource.{u,v,w,t}) (base : A.Sorts)
    (hOne : ∀ i : A.Sorts, base = i) (E : ExactEq A.source base) :
    (originalCoreQuotientCurrentSource A base hOne E).source =
      originalCoreQuotient A base hOne E := rfl

/-- At the genuine zero prefix the all-parent quotient source is
literally the canonical ORIGINAL quotient source. No initial quotient
homogeneity or age identification is an additional premise. -/
theorem originalCoreQuotientCurrentSource_initial_all
    (A : CurrentSource.{u,v,w,t}) (base : A.Sorts)
    (hOne : ∀ i : A.Sorts, base = i) (E : ExactEq A.source base) :
    originalExactAllCurrentQuotientCurrentSource A A (UnaryReduct.identity A.source)
      (ExactTraceTransport.identity A.source) base hOne E =
        originalCoreQuotientCurrentSource A base hOne E := by
  rfl

/-- Ordinary amalgamation belongs to the actual full quotient age;
there is no quotient-SAP premise or implicit replacement of its age. -/
theorem originalCoreQuotientCurrentSource_AP
    (A : CurrentSource.{u,v,w,t}) (base : A.Sorts)
    (hOne : ∀ i : A.Sorts, base = i) (E : ExactEq A.source base) :
    AgeAP (originalCoreQuotientCurrentSource A base hOne E).source := by
  letI : ∀ i, Countable (A.Point i) := A.countable
  exact (simultaneous_exact_quotients.{u,v,w,t,max u v} A.source A.homogeneous
    (originalExactSourceKernelFamily A base hOne E)
    (originalExactSourceKernelWords A base hOne E)
    (originalExactSourceKernelWords_relation A base hOne E) A.cco).amalgamation

/-- Strict rank decrease is now stated on the actual quotient
CurrentSource, at the SAME unique original sort, excluding the diagonal. -/
theorem originalCoreQuotientCurrentSource_rank_lt
    (A : CurrentSource.{u,v,w,t}) (base : A.Sorts)
    (hOne : ∀ i : A.Sorts, base = i) (E : ExactEq A.source base)
    (positive : (⊥ : ExactEq A.source base) < E) :
    originalDiversityRank (originalCoreQuotientCurrentSource A base hOne E) base <
      originalDiversityRank A base := by
  rw [originalDiversityRank_eq_natCard (originalCoreQuotientCurrentSource A base hOne E) base]
  exact original_exact_quotient_rank_lt A base hOne E positive

/-- The genuine initial selected quotient has ONE original occupancy
sort. Its source includes the finite and zero-step cases. -/
theorem original_initial_selected_quotient_one_sort
    (A : CurrentSource.{u,v,w,t}) (base : A.Sorts)
    (hOne : ∀ i : A.Sorts, base = i) (E : ExactEq A.source base)
    (c : OriginalOccupancy A A (UnaryReduct.identity A.source) base hOne E) :
    (Quotient.mk'' base : OriginalOccupancy A A
      (UnaryReduct.identity A.source) base hOne E) = c := by
  induction c using Quotient.inductionOn with
  | _ i => exact congrArg Quotient.mk'' (hOne i)

/-- The strict ORIGINAL rank drop applies to the LITERAL initial
selected source used by the B062 aligned quotient tower. No replacement
tower, quotient source or cardinal-drop provider is supplied. -/
theorem original_initial_selected_quotient_rank_lt
    (A : CurrentSource.{u,v,w,t}) (base : A.Sorts)
    (hOne : ∀ i : A.Sorts, base = i) (E : ExactEq A.source base)
    (positive : (⊥ : ExactEq A.source base) < E) :
    originalDiversityRank
      (originalExactSelectedQuotientCurrentSource A A (UnaryReduct.identity A.source)
        (ExactTraceTransport.identity A.source) base hOne E)
      (Quotient.mk'' base) < originalDiversityRank A base := by
  rw [originalDiversityRank_eq_natCard
    (originalExactSelectedQuotientCurrentSource A A (UnaryReduct.identity A.source)
      (ExactTraceTransport.identity A.source) base hOne E) (Quotient.mk'' base)]
  let rep := originalOccupancyRepresentative A A (UnaryReduct.identity A.source)
    base hOne E (Quotient.mk'' base)
  change Nat.card ((originalCoreQuotient A base hOne E).Atom rep rep) < originalDiversityRank A base
  calc
    Nat.card ((originalCoreQuotientCurrentSource A base hOne E).source.Atom rep rep) =
        Nat.card ((originalCoreQuotientCurrentSource A base hOne E).source.Atom base base) :=
      congrArg (fun i : A.Sorts =>
        Nat.card ((originalCoreQuotientCurrentSource A base hOne E).source.Atom i i))
        (hOne rep).symm
    _ < originalDiversityRank A base := original_exact_quotient_rank_lt A base hOne E positive

end
end CCO.AutomaticEPCore
