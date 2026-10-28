import CCO.SIR.Positive.Direct.ParentSeparation
import CCO.SIR.Positive.Direct.Realization

/-! Direct CCO of the original e/d/n two-sheet real source. All signed-cycle,
parent-separation and real realization obligations are proved in this branch;
no selector, NR2, quotient-language or standing CCO premise is used. -/

universe z

namespace CCO.SIR.Positive.Direct

/-- Every cycle-consistent finite partial diagram has an injective realization
in the actual original real source. Empty diagrams are included. -/
theorem injective_complete_of_cycles {V : Type z} (D : PartialDiagram source V)
    (hcycles : ∀ C : SimpleCycle D, CycleHom C) :
    ∃ f : DiagramHom D, f.IsInjective :=
  injective_realization_of_parent_separation D hcycles
    (fun _ _ h hn => n_edge_not_reachable D hcycles h hn)

/-- The semantic CCO headline for the literal carrier ℕ×Bool×ℕ and its original
three diversity atoms. This construction is independent of the sufficient
NR2/hereditary-selector route used by the other positive SIR theorem. -/
theorem semanticCCO : SemanticCCO.{0,0,z,0} source := by
  intro V D hcycles
  obtain ⟨f,_⟩ := injective_complete_of_cycles D hcycles
  exact ⟨f⟩

end CCO.SIR.Positive.Direct
