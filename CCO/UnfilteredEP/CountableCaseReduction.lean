import CCO.UnfilteredEP.RealExpansionUniverseLift
import CCO.UnfilteredEP.FiniteTagEP

/-! C104's genuine finite/infinite ORIGINAL-source case split.
The finite case constructs the actual safe tower and retains its unique
terminal tags and zero-chart readout. The infinite-case result remains
an explicit lemma input here and must be discharged by actual C95 in the
final source export; this helper is not a completed countable main theorem. -/

universe u v w r
namespace CCO.UnfilteredEP
open CCO.TerminalHiddenHN CCO.TerminalHiddenHN.RealExpansionData
noncomputable section
variable {ι : Type u} {X : ι → Type v} (S : AtomicSource.{u,v,w} ι X)
variable {G : Type r} [Group G] [∀ i : ι, MulAction G (X i)]
variable (H : HomogeneousSource S G) (ap : AgeAP S)
variable (cco : SemanticCCO.{u,v,max u v,w} S)

/-- Finite unary/binary symbols, faithful hereditary actual expansions,
reasonableness, Ramsey, and EP on the SAME original induced age.
Reduct-surjectivity and precompactness are fields/consequences of the
actual RealExpansionData, not additional provider premises. -/
def HasFiniteRelationalRamseyEPExpansion : Prop :=
  ∃ E : RealExpansionData.{u,v,w,max u v w,max u v w} S,
    E.Reasonable ∧ E.Ramsey ∧ E.EP

include H ap cco

/-- The finite source already gives the genuine recipe at the common
output universe, without any infinite-owner, proper-chart or EP premise. -/
theorem finite_original_unfiltered_expansion (finite : ∀ i, Finite (X i)) :
    HasFiniteRelationalRamseyEPExpansion S := by
  let B := initialFiniteOwnerStage S H ap cco finite
  obtain ⟨D,history,terminal,reasonable,ramsey,ep⟩ := finite_unfiltered_source B
  let E := finiteZeroChartData history terminal
  let F : RealExpansionData.{u,v,w,max u v w,max u v w} S :=
    universeLiftRealExpansion.{u,v,w,u,max u v,max u v w,max u v w} E
  exact ⟨F,universeLift_reasonable E reasonable,universeLift_Ramsey E ramsey,
    universeLift_EP E ep⟩

/-- A single original transitive sort is finite or infinite. This source
case split combines the ACTUAL finite branch with a separately proved
infinite source result, retaining ordinary AP and semantic HOM CCO. -/
theorem original_source_case_reduction (base : ι) (one : ∀ i : ι, base = i)
    (infiniteCase : (∀ i, Infinite (X i)) → HasFiniteRelationalRamseyEPExpansion S) :
    HasFiniteRelationalRamseyEPExpansion S := by
  classical
  cases finite_or_infinite (X base) with
  | inl finite =>
    apply finite_original_unfiltered_expansion S H ap cco
    intro i
    cases one i
    exact finite
  | inr infinite =>
    apply infiniteCase
    intro i
    cases one i
    exact infinite

end
end CCO.UnfilteredEP
