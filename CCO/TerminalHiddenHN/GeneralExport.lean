import CCO.TerminalHiddenHN.TerminalExport
import CCO.TerminalHiddenHN.UnaryLift
import CCO.PairSafeSplit.Terminal.Elimination

/-! The GENERAL source is terminalised before the terminal Ramsey theorem
is applied. Its actual safe-split history supplies a different finite
source and the literal reasonable unary reduct. No infinite-cover premise
is imposed on the original source. The final language keeps the finite
unary labels of this history and the terminal comparison predicates. -/

universe u v w r
namespace CCO.TerminalHiddenHN
noncomputable section
variable {ι : Type u} {X : ι → Type v} (S : CCO.AtomicSource.{u,v,w} ι X)
variable {G : Type r} [Group G] [∀ i, MulAction G (X i)]
variable (H : CCO.HomogeneousSource S G) (sap : CCO.AgeSAP S)
variable [∀ i, Countable (X i)]

/-- Source `thm:internal-v27-general-ramsey`. All terminal source
premises are discharged on the NEW source produced by actual finite
cover elimination. The original source need not have infinite covers.
Finite relationality, precompactness, same-map reasonableness and Ramsey
are retained separately; no expansion property is asserted. -/
theorem general_finite_relational_ramsey_expansion
    (cco : CCO.SemanticCCO.{u,v,max u v,w} S) :
    HasFiniteRelationalRamseyExpansion.{u,v,w,max u v w,max u v w} S := by
  obtain ⟨terminal,history,ht,hbound,hsap,hcco,htri,hcover,red,unary,hforget⟩ :=
    CCO.PairSafeSplit.Terminal.original_selected_finite_cover_elimination
      S H sap cco (fun i => inferInstance)
  letI : ∀ i, Countable (terminal.base.Point i) := terminal.base.countable
  have hTerminal := terminal_finite_relational_ramsey_expansion
    terminal.base.source terminal.base.homogeneous hsap hcover hcco
  have hReasonable : CCO.APCharacter.Towers.Reasonable red.forget := by
    rw [← hforget]
    exact unary.reasonable
  exact hasFiniteRelationalRamseyExpansion_of_unaryReduct red hReasonable hTerminal

end
end CCO.TerminalHiddenHN
