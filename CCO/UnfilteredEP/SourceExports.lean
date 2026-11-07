import CCO.UnfilteredEP.UnfilteredOwnerMain
import CCO.UnfilteredEP.CountableCaseReduction
import CCO.APRamseyReadout.GeneralExpansion

/-! The unfiltered source theorem on the ORIGINAL age. Ordinary AP and
semantic homomorphic cycle constrainedness construct the genuine safe
history. All terminal labels are retained. The infinite branch discharges
its actual synchronized hidden EP; the finite branch uses the separate
actual singleton-tag/zero-chart construction. No Ramsey, SAP, core,
terminality, hidden-class or EP provider is an input. -/

universe u v w r
namespace CCO.UnfilteredEP
open CCO.CloneTupleGeometry CCO.APRamseyReadout CCO.TerminalHiddenHN
noncomputable section
variable {ι : Type u} {X : ι → Type v} (S : AtomicSource.{u,v,w} ι X)
variable {G : Type r} [Group G] [∀ i : ι, MulAction G (X i)]
variable (H : HomogeneousSource S G) (ap : AgeAP S)
variable (cco : SemanticCCO.{u,v,max u v,w} S)
include H ap cco

/-- C95 at the original source: the actual safe history, full terminal
labels and normalized finite relational expansion are constructed from
ordinary AP. All four tuple contracts and the hidden/unary EP gates have
already been discharged, on one actual original induced age. -/
theorem infinite_original_unfiltered_expansion
    (base : ι) (one : ∀ i : ι, base = i)
    (countable : ∀ i, Countable (X i)) (infinite : ∀ i, Infinite (X i)) :
    HasFiniteRelationalRamseyEPExpansion S := by
  let B := initialOwnerStage S H ap cco countable infinite
  obtain ⟨D,history,terminal,_bound,_reduct,_unary,_forget⟩ :=
    B.finite_safe_terminalisation
  let F := defaultCharts D
  let priority := defaultReadoutPriority D terminal
  let E := actualOwnerNormalizedData D terminal F priority history
  obtain ⟨reasonable,ramsey,ep,_precompact⟩ :=
    genuine_owner_unfiltered_expansion D terminal F priority base one history
  exact ⟨E,reasonable,ramsey,ep⟩

/-- C104 / thm:ep-unfiltered-main: a countable one-sort homogeneous
symmetric atomic source with ordinary AP and semantic HOM CCO admits a
reasonable precompact finite unary/binary Ramsey expansion with EP.
Both finite and infinite original sources are covered. Every EP witness
fixes one old induced host before ALL competing full expansions. -/
theorem countable_original_unfiltered_expansion
    (base : ι) (one : ∀ i : ι, base = i)
    (countable : ∀ i, Countable (X i)) :
    HasFiniteRelationalRamseyEPExpansion S :=
  original_source_case_reduction S H ap cco base one
    (infinite_original_unfiltered_expansion S H ap cco base one countable)

/-- Explicit reduct-surjectivity and precompactness of the SAME expansion
in the source theorem. They are intrinsic actual-data fields, not new
assumptions and not a second independently chosen expansion. -/
theorem countable_original_unfiltered_expansion_full
    (base : ι) (one : ∀ i : ι, base = i)
    (countable : ∀ i, Countable (X i)) :
    ∃ E : RealExpansionData.{u,v,w,max u v w,max u v w} S,
      E.Reasonable ∧ E.Ramsey ∧ E.EP ∧
      (∀ A, Nonempty (E.Expansion A)) ∧ (∀ A, Finite (E.Expansion A)) := by
  obtain ⟨E,reasonable,ramsey,ep⟩ :=
    countable_original_unfiltered_expansion S H ap cco base one countable
  exact ⟨E,reasonable,ramsey,ep,E.nonempty,E.finite_expansions⟩

end
end CCO.UnfilteredEP
