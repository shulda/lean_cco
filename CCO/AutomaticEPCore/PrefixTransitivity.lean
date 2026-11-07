import CCO.AutomaticEPCore.PhaseActiveAction

/-! The inner source induction is over ALL actual prefixes of the SAME
certified tower. The kernel F is fixed on the original carrier. Every
identity-gate step uses its own actual phase-selected odd element in F;
that SAME element is then used over every active parent of that step. -/

universe u v w t
namespace CCO.AutomaticEPCore
open CCO.APCharacter CCO.APCharacter.Towers
open CCO.APCharacter.SourceAge CCO.ExactEPGeometry
open CCO.RigidGroupoid.Geometry
open CCO.ParityHasse.Original
noncomputable section

/-- C39–C50 source step for the bound canonical least-positive FULL-EXACT
F. Actual original gate positivity selects retained/identity branches;
the two one-step providers already construct all phase and child duties. -/
theorem least_exact_prefix_transitive_step
    (A : CurrentSource.{u,v,w,t}) (base : A.Sorts)
    (hOne : ∀ i : A.Sorts, base = i)
    (positive : (⊥ : ExactEq A.source base) < leastPositiveExact A base)
    {s next : CertifiedGateTower.ExactPrefix A}
    (step : CertifiedGateTower.Step s next)
    (previous : exactFunctionalPrefixTransitive A s.current s.reduct
      base hOne (leastPositiveExact A base)) :
    exactFunctionalPrefixTransitive A next.current next.reduct
      base hOne (leastPositiveExact A base) := by
  classical
  let choice : CertifiedGateTower.GateChoice s := Classical.choose step
  rw [certifiedStep_witness_is_actual_successor step]
  let K := MaximalGate.kernel s.current.source s.current.homogeneous
    (evenColourEq s.current.source s.current.homogeneous choice.c)
    (connectivityColourEq s.current.source s.current.homogeneous choice.c) choice.M
  change exactFunctionalPrefixTransitive A
    (SingleStep.successor s.current choice.phase)
    (s.reduct.compose (SingleStep.projection s.current choice.phase))
    base hOne (leastPositiveExact A base)
  by_cases identityGate : certifiedStepOriginalGate A base hOne step = ⊥
  · exact exact_functional_prefix_transitive_identity_fixed_base
      A s.current s.reduct s.transport s.product base hOne K choice.phase
      (leastPositiveExact A base) positive identityGate previous
  · apply exact_functional_prefix_transitive_retained_fixed_base
      A s.current s.reduct s.transport s.product base hOne K choice.phase
      (leastPositiveExact A base) _ previous
    exact leastPositiveExact_le A base
      (certifiedStepOriginalGate A base hOne step)
      (bot_lt_iff_ne_bot.mpr identityGate)

/-- C39–C51 at EVERY finite prefix. This is genuine induction on the
given source history, not a terminal-only orbit assumption. The original
diversity-rank induction remains the distinct outer induction. -/
theorem least_exact_prefix_transitive_history
    (A : CurrentSource.{u,v,w,t}) (base : A.Sorts)
    (hOne : ∀ i : A.Sorts, base = i)
    (positive : (⊥ : ExactEq A.source base) < leastPositiveExact A base)
    {s next : CertifiedGateTower.ExactPrefix A}
    (history : History CertifiedGateTower.Step s next)
    (initial : exactFunctionalPrefixTransitive A s.current s.reduct
      base hOne (leastPositiveExact A base)) :
    exactFunctionalPrefixTransitive A next.current next.reduct
      base hOne (leastPositiveExact A base) := by
  exact History.preserves
    (fun p : CertifiedGateTower.ExactPrefix A =>
      exactFunctionalPrefixTransitive A p.current p.reduct
        base hOne (leastPositiveExact A base))
    (fun {_ _} step previous =>
      least_exact_prefix_transitive_step A base hOne positive step previous)
    history initial

/-- An identity member of the ACTUAL gate list supplies positivity of
the SAME F used at all prefixes. No positive-F provider is assumed. -/
theorem identity_history_gate_least_exact_positive
    (A : CurrentSource.{u,v,w,t}) (base : A.Sorts)
    (hOne : ∀ i : A.Sorts, base = i)
    {s next : CertifiedGateTower.ExactPrefix A}
    (history : History CertifiedGateTower.Step s next)
    (identityGate : (⊥ : ExactEq A.source base) ∈
      certifiedHistoryOriginalGates A base hOne history) :
    (⊥ : ExactEq A.source base) < leastPositiveExact A base := by
  induction history with
  | nil _ => cases identityGate
  | cons step tail ih =>
    rcases List.mem_cons.mp identityGate with head | remaining
    · exact (certified_identity_step_least_exact
        A base hOne step head.symm).1
    · exact ih remaining

/-- The identity-gate branch has actual H_F transitivity on EVERY final
F-occupancy class, discharged from its own source steps and true initial
one-sort prefix. Finite sources and zero-stage histories are covered. -/
theorem identity_history_final_least_exact_transitive
    (A : CurrentSource.{u,v,w,t}) (base : A.Sorts)
    (hOne : ∀ i : A.Sorts, base = i)
    {terminal : CertifiedGateTower.ExactPrefix A}
    (history : History CertifiedGateTower.Step (CertifiedGateTower.initial A) terminal)
    (identityGate : (⊥ : ExactEq A.source base) ∈
      certifiedHistoryOriginalGates A base hOne history) :
    exactFunctionalPrefixTransitive A terminal.current terminal.reduct
      base hOne (leastPositiveExact A base) := by
  exact least_exact_prefix_transitive_history A base hOne
    (identity_history_gate_least_exact_positive A base hOne history identityGate)
    history (exact_functional_prefix_transitive_initial A base hOne _)

end
end CCO.AutomaticEPCore
