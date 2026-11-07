import CCO.AutomaticEPCore.FunctionalOriginal
import CCO.TerminalLattice.OriginalQuotientInvariantFinite
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.GroupTheory.GroupAction.Basic

/-! C30-C31: actual quotient invariant relations make the group of
equivariant quotient permutations finite. In particular each such
permutation has finite order BEFORE any terminality argument. -/

universe u v w r
namespace CCO.UnfilteredEP
open CCO.ParityHasse.Original CCO.TerminalLattice CCO.AutomaticEPCore
noncomputable section
variable {ι : Type u} {X : ι → Type v} (S : AtomicSource.{u,v,w} ι X)
variable {G : Type r} [Group G] [∀ i, MulAction G (X i)]
variable (H : HomogeneousSource S G) {i : ι} (J : ColourEq S i)

abbrev QuotientFunctionalGroup :=
  letI : MulAction G (Quotient J.val) := originalQuotientAction S H J
  OriginalFunctionalGroup G (Quotient J.val)

/-- The graph is invariant under exactly the original ambient group. -/
def quotientFunctionalGraph (f : QuotientFunctionalGroup S H J) :
    OriginalInvariantQuotientState S H J := by
  letI : MulAction G (Quotient J.val) := originalQuotientAction S H J
  exact ⟨fun x y => f.val x = y,by
    intro g x y h
    change f.val (g • x) = g • y
    rw [f.property,h]⟩

theorem quotientFunctionalGraph_injective :
    Function.Injective (quotientFunctionalGraph S H J) := by
  intro f g h
  apply Subtype.ext
  apply Equiv.ext
  intro x
  have he := congrFun (congrFun (congrArg Subtype.val h) x) (f.val x)
  exact ((Iff.of_eq he).mp rfl).symm

/-- C30: this finiteness concerns invariant binary relations, not the
possibly infinite actual quotient carrier. -/
theorem quotient_invariant_relations_finite :
    Finite (OriginalInvariantQuotientState S H J) :=
  originalInvariantQuotientState_finite S H J

theorem quotient_functional_group_finite : Finite (QuotientFunctionalGroup S H J) := by
  letI := quotient_invariant_relations_finite S H J
  exact Finite.of_injective _ (quotientFunctionalGraph_injective S H J)

/-- C31: recurrence of invariant graphs gives a positive identity power.
No FULL terminality, SAP, CCO, Ramsey or EP is used. -/
theorem quotient_functional_finite_order (f : QuotientFunctionalGroup S H J) :
    ∃ n : ℕ, 0 < n ∧ f ^ n = 1 := by
  letI := quotient_functional_group_finite S H J
  exact (isOfFinOrder_of_finite f).exists_pow_eq_one

end
end CCO.UnfilteredEP
