import CCO.AutomaticEPCore.PrefixTransitivity

/-! C51's same-F-occupancy separation is an actual original bipartite
orbital, constructed from the proved whole-prefix H_F action. This is
one branch of the outer original-rank argument, not its quotient branch. -/

universe u v w t
namespace CCO.AutomaticEPCore
open CCO.APCharacter.Towers CCO.ExactEPGeometry
open CCO.ParityHasse.Original
noncomputable section

/-- Any two distinct types in one actual E-occupancy orbit have a
functional bipartite original atom between them. No quotient separator,
marked automorphism action or extra source provider is supplied. -/
theorem exact_functional_occupancy_bipartite_separator
    (A B : CurrentSource.{u,v,w,t}) (P : UnaryReduct A.source B.source)
    (base : A.Sorts) (hOne : ∀ i : A.Sorts, base = i)
    (E : ExactEq A.source base)
    (transitive : exactFunctionalPrefixTransitive A B P base hOne E)
    (s t : B.Sorts) (hne : s ≠ t)
    (occupancy : (originalExactOccupancySetoid A B P base hOne E).r s t) :
    ∃ a : A.source.Atom base base,
      (atomGraph A.source a).IsBipartite ∧
        originalAtomTable A B P base hOne a s t := by
  obtain ⟨h,move⟩ := transitive s t occupancy
  have nonidentity : h.val ≠ 1 := by
    intro he
    rw [he,original_functional_type_perm_one] at move
    exact hne move
  obtain ⟨a,graph,bipartite⟩ :=
    original_functional_bipartite_atom A.source A.homogeneous h.val nonidentity
  obtain ⟨x,y,hxy⟩ :=
    (original_functional_type_perm_iff A B P base hOne h.val s t).mp move
  exact ⟨a,bipartite,x,y,(graph _ _).mpr hxy⟩

/-- C51's terminal receiving theorem. Positivity and all-prefix H_F
transitivity are discharged by the SAME actual source history. The outer
different-F-class quotient/rank branch remains a separate obligation. -/
theorem identity_history_same_occupancy_bipartite_separator
    (A : CurrentSource.{u,v,w,t}) (base : A.Sorts)
    (hOne : ∀ i : A.Sorts, base = i)
    {terminal : CertifiedGateTower.ExactPrefix A}
    (history : History CertifiedGateTower.Step (CertifiedGateTower.initial A) terminal)
    (identityGate : (⊥ : ExactEq A.source base) ∈
      certifiedHistoryOriginalGates A base hOne history)
    (s t : terminal.current.Sorts) (hne : s ≠ t)
    (occupancy : (originalExactOccupancySetoid A terminal.current terminal.reduct
      base hOne (leastPositiveExact A base)).r s t) :
    ∃ a : A.source.Atom base base,
      (atomGraph A.source a).IsBipartite ∧
        originalAtomTable A terminal.current terminal.reduct base hOne a s t := by
  exact exact_functional_occupancy_bipartite_separator
    A terminal.current terminal.reduct base hOne (leastPositiveExact A base)
    (identity_history_final_least_exact_transitive A base hOne history identityGate)
    s t hne occupancy

end
end CCO.AutomaticEPCore
