import CCO.UnfilteredEP.QuotientOrbitInterval
import CCO.APRamseyReadout.ActualSource

/-! C33: terminality is applied only after the actual finite cyclic
orbit interval has been constructed. Every equivariant quotient return
permutation is identity; products of return maps are identity as well. -/

universe u v w r
namespace CCO.UnfilteredEP
open CCO.ParityHasse.Original CCO.TerminalLattice CCO.AutomaticEPCore
open CCO.APRamseyReadout CCO.CloneTupleGeometry
noncomputable section
variable {ι : Type u} {X : ι → Type v} (S : AtomicSource.{u,v,w} ι X)
variable {G : Type r} [Group G] [∀ i, MulAction G (X i)]
variable (H : HomogeneousSource S G) {i : ι} (J : ColourEq S i)

/-- The terminal premise ranges over EVERY higher FULL invariant
equivalence, not just a represented coordinate sublattice. -/
theorem quotient_functional_eq_one_of_no_finite_interval
    (terminal : ∀ K : ColourEq S i, J < K →
      ∀ a, Infinite (RelativeClass J.val K.val a))
    (f : QuotientFunctionalGroup S H J) : f = 1 := by
  by_contra hf
  obtain ⟨K,hJK,hfinite,_,_⟩ := quotient_nontrivial_finite_interval S H J f hf
  obtain ⟨a⟩ := S.nonemptySort i
  letI := terminal K hJK a
  exact (hfinite a).false

variable (B : OwnerStage.{u,v,w}) (ht : B.Terminal)
include ht

/-- Actual source instance of `lem:ep-terminal-holonomy`. It permits
every FULL quotient, not only the selected visible MI coordinates. -/
theorem terminal_quotient_holonomy {i : B.Sorts}
    (J : ColourEq (cloneSource B) i)
    (f : QuotientFunctionalGroup (cloneSource B) (cloneHomogeneous B) J) : f = 1 :=
  quotient_functional_eq_one_of_no_finite_interval
    (cloneSource B) (cloneHomogeneous B) J
    (fun K hJK a => B.terminal_interval_infinite ht J K hJK a) f

theorem terminal_quotient_holonomy_apply {i : B.Sorts}
    (J : ColourEq (cloneSource B) i)
    (f : QuotientFunctionalGroup (cloneSource B) (cloneHomogeneous B) J)
    (q : Quotient J.val) : f.val q = q := by
  rw [terminal_quotient_holonomy B ht J f]
  rfl

/-- Closed return chains stay in the SAME quotient functional group;
there is no choice of new group, quotient action or orbit representatives. -/
theorem terminal_quotient_return_chain {i : B.Sorts}
    (J : ColourEq (cloneSource B) i)
    (maps : List (QuotientFunctionalGroup (cloneSource B) (cloneHomogeneous B) J)) :
    maps.prod = 1 :=
  terminal_quotient_holonomy B ht J maps.prod

end
end CCO.UnfilteredEP
